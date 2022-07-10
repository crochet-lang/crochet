use std::collections::{HashMap, HashSet};

use crochet_ast::*;

use crate::substitutable::Substitutable;

use super::context::{Context, Env};
use super::infer_type_ann::*;
use super::substitutable::Subst;
use super::types::{self, freeze_scheme, Scheme, Type, Variant};
use super::util::{generalize, normalize};

pub fn infer_prog(prog: &Program) -> Result<Context, String> {
    let mut ctx: Context = Context::default();

    // TODO: figure out how report multiple errors
    for stmt in &prog.body {
        match stmt {
            Statement::VarDecl {
                declare,
                init,
                pattern,
                ..
            } => {
                match declare {
                    true => {
                        match pattern {
                            Pattern::Ident(BindingIdent { id, type_ann, .. }) => {
                                match type_ann {
                                    Some(type_ann) => {
                                        let scheme = infer_scheme(type_ann, &ctx);
                                        ctx.values
                                            .insert(id.name.to_owned(), freeze_scheme(scheme));
                                    }
                                    None => {
                                        // A type annotation should always be provided when using `declare`
                                        return Err(String::from(
                                            "missing type annotation in declare statement",
                                        ));
                                    }
                                }
                            }
                            _ => todo!(),
                        }
                    }
                    false => {
                        // An initial value should always be used when using a normal `let` statement
                        let init = init.as_ref().unwrap();

                        let type_param_map = HashMap::new();
                        let (ps, pa, pt) = infer_pattern(pattern, &ctx, &type_param_map)?;

                        let (is, it) = infer(&ctx, init)?;

                        // unifies initializer and pattern
                        let s = unify(&pt, &it, &ctx)?;
                        
                        // infer_pattern can generate a non-empty Subst when the pattern includes
                        // a type annotation.
                        let s = compose_many_subs(&[is, ps, s]);

                        // We need to apply the substitutions from the constraint solver to the
                        // pattern and initializer types before checking if they're subtypes since
                        // since is_subtype() ignores type variables.
                        // let pt = pt.apply(&s);
                        // let it = it.apply(&s);

                        // If the initializer is not a subtype of what we're assigning it
                        // to, return an error.
                        // TODO: Add `is_subtype` check... or handle it as part of the `unify` call above.
                        // if !is_subtype(&it, &pt, &ctx)? {
                        //     return Err(String::from(
                        //         "value is not a subtype of decl's declared type",
                        //     ));
                        // }

                        // Inserts the new variables from infer_pattern() into the
                        // current context.
                        for (name, scheme) in pa {
                            let scheme = normalize(&scheme.apply(&s), &ctx);
                            ctx.values.insert(name, freeze_scheme(scheme));
                        }
                    }
                };
            }
            Statement::TypeDecl {
                id,
                type_ann,
                type_params,
                ..
            } => {
                let scheme = infer_scheme_with_type_params(type_ann, type_params, &ctx);
                ctx.types.insert(id.name.to_owned(), freeze_scheme(scheme));
            }
            Statement::Expr { expr, .. } => {
                // We ignore the type that was inferred, we only care that
                // it succeeds since we aren't assigning it to variable.
                infer_expr(&ctx, expr)?;
            }
        };
    }

    Ok(ctx)
}

pub fn infer_expr(ctx: &Context, expr: &Expr) -> Result<Scheme, String> {
    let (s, t) = infer(ctx, expr)?;
    Ok(close_over(&s, &t, ctx))
}

// closeOver :: (Map.Map TVar Type, Type) -> Scheme
// closeOver (sub, ty) = normalize sc
//   where sc = generalize emptyTyenv (apply sub ty)
fn close_over(s: &Subst, t: &Type, ctx: &Context) -> Scheme {
    let empty_env = Env::default();
    normalize(&generalize(&empty_env, &t.to_owned().apply(s)), ctx)
}

fn infer(ctx: &Context, expr: &Expr) -> Result<(Subst, Type), String> {
    match expr {
        Expr::App(App { lam, args, .. }) => {
            let (s1, t1) = infer(ctx, lam)?;
            let (mut args_ss, args_ts): (Vec<_>, Vec<_>) =
                args.iter().filter_map(|arg| infer(ctx, arg).ok()).unzip();

            let tv = ctx.fresh_var();
            // Are we missing an `apply()` call here?
            // s3       <- unify (apply s2 t1) (TArr t2 tv)
            let s3 = unify(&t1, &ctx.lam(args_ts, Box::from(tv.clone())), ctx)?;

            // ss = [s3, ...args_ss, s1]
            let mut ss = vec![s3.clone()];
            ss.append(&mut args_ss);
            ss.push(s1);

            // return (s3 `compose` s2 `compose` s1, apply s3 tv)
            Ok((compose_many_subs(&ss), tv.apply(&s3)))
            // TODO:
            // - partial application
            // - subtyping
        }
        Expr::Fix(Fix { expr, .. }) => {
            let (s1, t) = infer(ctx, expr)?;
            let tv = ctx.fresh_var();
            let s2 = unify(&ctx.lam(vec![tv.clone()], Box::from(tv.clone())), &t, ctx)?;
            Ok((compose_subs(&s2, &s1), tv.apply(&s2)))
        }
        Expr::Ident(Ident { name, .. }) => {
            // TODO: return an error if the lookup fails
            let s = Subst::new();
            let t = ctx.lookup_value(name);
            Ok((s, t))
        }
        Expr::IfElse(IfElse {
            cond,
            consequent,
            alternate,
            ..
        }) => match alternate {
            Some(alternate) => {
                let (s1, t1) = infer(ctx, cond)?;
                let (s2, t2) = infer(ctx, consequent)?;
                let (s3, t3) = infer(ctx, alternate)?;
                let s4 = unify(&t1, &ctx.prim(Primitive::Bool), ctx)?;
                let t = union_types(&t2, &t3, ctx);
                Ok((compose_many_subs(&[s1, s2, s3, s4]), t))
            }
            None => {
                let (s1, t1) = infer(ctx, cond)?;
                let (s2, t2) = infer(ctx, consequent)?;
                let s3 = unify(&t1, &ctx.prim(Primitive::Bool), ctx)?;
                let t = t2;
                Ok((compose_many_subs(&[s1, s2, s3]), t))
            }
        },
        Expr::JSXElement(_) => todo!(),
        Expr::Lambda(Lambda {
            params,
            body,
            is_async: _,
            return_type,
            type_params,
            ..
        }) => {
            let mut new_ctx = ctx.clone();

            let type_params_map: HashMap<String, Type> = match type_params {
                Some(params) => params
                    .iter()
                    .map(|param| (param.name.name.to_owned(), new_ctx.fresh_var()))
                    .collect(),
                None => HashMap::default(),
            };

            let params: Result<Vec<(Subst, Type)>, String> = params
                .iter()
                .map(|param| {
                    let (subst, assump, param_type) =
                        infer_pattern(param, &new_ctx, &type_params_map)?;

                    // Inserts any new variables introduced by infer_pattern() into
                    // the current context.
                    for (name, scheme) in assump {
                        new_ctx.values.insert(name, scheme);
                    }

                    Ok((subst, param_type))
                })
                .collect();

            let (ss, ts): (Vec<_>, Vec<_>) = params?.iter().cloned().unzip();

            let (rs, rt) = infer(&new_ctx, body)?;

            // TODO: copy over the next_id from new_ctx
            ctx.state.count.set(new_ctx.state.count.get());

            let s = match return_type {
                Some(return_type) => unify(&rt, &infer_type_ann(return_type, ctx), ctx)?,
                None => Subst::default(),
            };
            let t = ctx.lam(ts, Box::from(rt));
            let s = compose_subs(&s, &compose_subs(&rs, &compose_many_subs(&ss)));

            Ok((s.clone(), t.apply(&s)))
        }
        Expr::Let(Let {
            pattern,
            init,
            body,
            ..
        }) => {
            let (is, it) = infer(ctx, init)?;

            match pattern {
                Some(pat) => {
                    let mut new_ctx = ctx.clone();
                    new_ctx.types = ctx.types.apply(&is);
                    // TODO: update `infer_pattern` to generalize patterns
                    // let t = generalize(&new_ctx.types, &it);

                    let type_param_map = HashMap::new();
                    let (ps, pa, pt) = infer_pattern(pat, &new_ctx, &type_param_map)?;

                    // unifies initializer and pattern
                    let s = unify(&pt, &it, &new_ctx)?;

                    // infer_pattern can generate a non-empty Subst when the pattern includes
                    // a type annotation.
                    let s = compose_subs(&ps, &s);

                    let pa = pa.apply(&s);
                    for (k, v) in pa.iter() {
                        new_ctx.values.insert(k.to_owned(), v.to_owned());
                    }

                    infer(&new_ctx, body.as_ref())
                }
                // handles: let _ => ... and non-final non-let expressions
                None => {
                    todo!()
                }
            }

            // let (subst, assump, param_type) = infer_pattern(param, &mut ctx, &type_params_map)?;
        }
        Expr::LetExpr(_) => todo!(),
        Expr::Lit(lit) => {
            let s = Subst::new();
            let t = ctx.lit(lit.to_owned());
            Ok((s, t))
        }
        Expr::Op(Op {op, left, right, ..}) => {
            // TODO: check what `op` is and handle comparison operators
            // differently from arithmetic operators
            let (s1, t1) = infer(ctx, left)?;
            let (s2, t2) = infer(ctx, right)?;
            let s3 = unify(&t1, &ctx.prim(Primitive::Num), ctx)?;
            let s4 = unify(&t2, &ctx.prim(Primitive::Num), ctx)?;
            let t = match op {
                BinOp::Add => ctx.prim(Primitive::Num),
                BinOp::Sub => ctx.prim(Primitive::Num),
                BinOp::Mul => ctx.prim(Primitive::Num),
                BinOp::Div => ctx.prim(Primitive::Num),
                BinOp::EqEq => ctx.prim(Primitive::Bool),
                BinOp::NotEq => ctx.prim(Primitive::Bool),
                BinOp::Gt => ctx.prim(Primitive::Bool),
                BinOp::GtEq => ctx.prim(Primitive::Bool),
                BinOp::Lt => ctx.prim(Primitive::Bool),
                BinOp::LtEq => ctx.prim(Primitive::Bool),
            };
            Ok((compose_many_subs(&[s1, s2, s3, s4]), t))
        }
        Expr::Obj(_) => todo!(),
        Expr::Await(_) => todo!(),
        Expr::Tuple(_) => todo!(),
        Expr::Member(_) => todo!(),
        Expr::Empty(_) => todo!(),
    }
}

fn unify(t1: &Type, t2: &Type, ctx: &Context) -> Result<Subst, String> {
    match (&t1.variant, &t2.variant) {
        (Variant::Var, _) => bind(&t1.id, t2),
        (_, Variant::Var) => bind(&t2.id, t1),
        (Variant::Lam(lam1), Variant::Lam(lam2)) => {
            let mut s = Subst::new();
            for (p1, p2) in lam1.params.iter().zip(&lam2.params) {
                let s1 = unify(&p1.apply(&s), &p2.apply(&s), ctx)?;
                s = compose_subs(&s, &s1);
            }
            let s1 = unify(&lam1.ret.apply(&s), &lam2.ret, ctx)?;
            Ok(compose_subs(&s, &s1))
        }
        (Variant::Prim(prim1), Variant::Prim(prim2)) => {
            if prim1 == prim2 {
                Ok(Subst::default())
            } else {
                Err(format!("{prim1} and {prim2} do not unify"))
            }
        }
        (Variant::Lit(lit1), Variant::Lit(lit2)) => {
            if lit1 == lit2 {
                Ok(Subst::default())
            } else {
                Err(format!("{lit1} and {lit2} do not unify"))
            }
        }
        (Variant::Lit(lit), Variant::Prim(prim)) => {
            let is_subtype = match (lit, prim) {
                (types::Lit::Num(_), Primitive::Num) => true,
                (types::Lit::Str(_), Primitive::Str) => true,
                (types::Lit::Bool(_), Primitive::Bool) => true,
                (_, _) => false,
            };
            if is_subtype {
                Ok(Subst::default())
            } else {
                Err(format!("{lit} and {prim} do not unify"))
            }
        }
        (_, _) => todo!(),
    }
}

fn bind(id: &i32, t: &Type) -> Result<Subst, String> {
    // | t == TVar a     = return nullSubst
    // | occursCheck a t = throwError $ InfiniteType a t
    // | otherwise       = return $ Map.singleton a t
    if &t.id == id {
        Ok(Subst::default())
    } else if occurs_check(id, t) {
        Err(String::from("InfiniteType"))
    } else {
        let mut result = Subst::default();
        result.insert(id.to_owned(), t.to_owned());
        Ok(result)
    }
}

fn occurs_check(id: &i32, t: &Type) -> bool {
    t.ftv().contains(id)
}

fn compose_subs(s1: &Subst, s2: &Subst) -> Subst {
    let mut result: Subst = s2.iter().map(|(id, tv)| (*id, tv.apply(s1))).collect();
    result.extend(s1.to_owned());
    result
}

// subs are composed from left to right with ones to the right
// being applied to all of the ones to the left.
fn compose_many_subs(subs: &[Subst]) -> Subst {
    subs.iter().fold(Subst::new(), |accum, next| {
        let mut result: Subst = compose_subs(&accum, next);
        result.extend(accum);
        result
    })
}

type Assump = HashMap<String, Scheme>;

// Everywhere we see contraints.push() we need to replace that we a call to `unify()`
// and we need to collect the Substs produced as part of the return value

// NOTE: The caller is responsible for inserting any new variables introduced
// into the appropriate context.
fn infer_pattern(
    pat: &Pattern,
    ctx: &Context,
    type_param_map: &HashMap<String, Type>,
) -> Result<(Subst, Assump, Type), String> {
    // Keeps track of all of the variables the need to be introduced by this pattern.
    let mut new_vars: HashMap<String, Scheme> = HashMap::new();

    let pat_type = infer_pattern_rec(pat, ctx, &mut new_vars)?;

    // If the pattern had a type annotation associated with it, we infer type of the
    // type annotation and add a constraint between the types of the pattern and its
    // type annotation.
    match get_type_ann(pat) {
        Some(type_ann) => {
            let type_ann_ty = infer_type_ann_with_params(&type_ann, ctx, type_param_map);
            let s = unify(&type_ann_ty, &pat_type, ctx)?;
            Ok((s, new_vars, type_ann_ty))
        }
        None => Ok((Subst::new(), new_vars, pat_type)),
    }
}

fn get_type_ann(pat: &Pattern) -> Option<TypeAnn> {
    match pat {
        Pattern::Ident(BindingIdent { type_ann, .. }) => type_ann.to_owned(),
        Pattern::Rest(RestPat { type_ann, .. }) => type_ann.to_owned(),
        Pattern::Object(ObjectPat { type_ann, .. }) => type_ann.to_owned(),
        Pattern::Array(ArrayPat { type_ann, .. }) => type_ann.to_owned(),
        Pattern::Lit(_) => None,
        Pattern::Is(_) => None,
    }
}

fn infer_pattern_rec(pat: &Pattern, ctx: &Context, assump: &mut Assump) -> Result<Type, String> {
    match pat {
        Pattern::Ident(BindingIdent { id, .. }) => {
            let tv = ctx.fresh_var();
            let scheme = Scheme::from(&tv);
            if assump.insert(id.name.to_owned(), scheme).is_some() {
                return Err(String::from("Duplicate identifier in pattern"));
            }
            Ok(tv)
        }
        Pattern::Lit(LitPat { lit, .. }) => Ok(ctx.lit(lit.to_owned())),
        Pattern::Is(IsPat { id, is_id, .. }) => {
            let ty = match is_id.name.as_str() {
                "string" => ctx.prim(types::Primitive::Str),
                "number" => ctx.prim(types::Primitive::Num),
                "boolean" => ctx.prim(types::Primitive::Bool),
                // The alias type will be used for `instanceof` of checks, but
                // only if the definition of the alias is an object type with a
                // `constructor` method.
                name => ctx.alias(name, None),
            };
            let scheme = generalize(&ctx.types, &ty);
            if assump.insert(id.name.to_owned(), scheme).is_some() {
                return Err(String::from("Duplicate identifier in pattern"));
            }
            Ok(ty)
        }
        Pattern::Rest(RestPat { arg, .. }) => infer_pattern_rec(arg.as_ref(), ctx, assump),
        Pattern::Array(ArrayPat { elems, .. }) => {
            let elems: Result<Vec<Type>, String> = elems
                .iter()
                .map(|elem| {
                    match elem {
                        Some(elem) => match elem {
                            Pattern::Rest(rest) => {
                                let rest_ty = infer_pattern_rec(rest.arg.as_ref(), ctx, assump)?;
                                Ok(ctx.rest(rest_ty))
                            }
                            _ => infer_pattern_rec(elem, ctx, assump),
                        },
                        None => {
                            // TODO: figure how to ignore gaps in the array
                            todo!()
                        }
                    }
                })
                .collect();

            Ok(ctx.tuple(elems?))
        }
        Pattern::Object(ObjectPat { props, .. }) => {
            let mut rest_opt_ty: Option<Type> = None;
            let props: Vec<types::TProp> = props
                .iter()
                .filter_map(|prop| {
                    match prop {
                        // re-assignment, e.g. {x: new_x, y: new_y} = point
                        ObjectPatProp::KeyValue(KeyValuePatProp { key, value }) => {
                            // TODO: bubble the error up from infer_patter_rec() if there is one.
                            let value_type = infer_pattern_rec(value, ctx, assump).unwrap();

                            Some(types::TProp {
                                name: key.name.to_owned(),
                                optional: false,
                                ty: value_type,
                            })
                        }
                        ObjectPatProp::Assign(AssignPatProp { key, value: _, .. }) => {
                            // We ignore the value for now, we can come back later to handle
                            // default values.
                            println!("AssignPatProp = {:#?}", key);

                            let tv = ctx.fresh_var();
                            let scheme = Scheme::from(&tv);
                            if assump.insert(key.name.to_owned(), scheme).is_some() {
                                todo!("return an error");
                            }

                            Some(types::TProp {
                                name: key.name.to_owned(),
                                optional: false,
                                ty: tv,
                            })
                        }
                        ObjectPatProp::Rest(rest) => {
                            // TypeScript doesn't support spreading/rest in types so instead we
                            // need to turn:
                            // {x, y, ...rest}
                            // into:
                            // {x: A, y: B} & C
                            // we also need some way to specify that C is an object type of some
                            // sort... maybe it'll just fall out when we trying to unify some other
                            // object type with an intersection type.
                            // essentially C = other_object_type - {x: A, y: B}
                            // TODO: panic if rest_opt_ty is not None, it means that the parser has
                            // failed to ensure that there's only one rest pattern in an object pattern

                            // TODO: bubble the error up from infer_patter_rec() if there is one.
                            rest_opt_ty = infer_pattern_rec(rest.arg.as_ref(), ctx, assump).ok();
                            None
                        }
                    }
                })
                .collect();

            let obj_type = ctx.object(props);

            match rest_opt_ty {
                Some(rest_ty) => Ok(ctx.intersection(vec![obj_type, rest_ty])),
                None => Ok(obj_type),
            }
        }
    }
}

// dedupe with constraint_solver.rs
fn flatten_types(ty: &Type) -> Vec<Type> {
    match &ty.variant {
        Variant::Union(types) => types.iter().flat_map(flatten_types).collect(),
        _ => vec![ty.to_owned()],
    }
}

// dedupe with constraint_solver.rs
fn union_types(t1: &Type, t2: &Type, ctx: &Context) -> Type {
    let mut types: Vec<Type> = vec![];
    types.extend(flatten_types(t1));
    types.extend(flatten_types(t2));

    let types_set: HashSet<_> = types.iter().cloned().collect();

    let prim_types: HashSet<_> = types_set
        .iter()
        .cloned()
        .filter(|ty| matches!(ty.variant, Variant::Prim(_)))
        .collect();
    let lit_types: HashSet<_> = types_set
        .iter()
        .cloned()
        .filter(|ty| match &ty.variant {
            // Primitive types subsume corresponding literal types
            Variant::Lit(lit) => match lit {
                types::Lit::Num(_) => !prim_types.contains(&ctx.prim(Primitive::Num)),
                types::Lit::Bool(_) => !prim_types.contains(&ctx.prim(Primitive::Bool)),
                types::Lit::Str(_) => !prim_types.contains(&ctx.prim(Primitive::Str)),
                types::Lit::Null => !prim_types.contains(&ctx.prim(Primitive::Null)),
                types::Lit::Undefined => !prim_types.contains(&ctx.prim(Primitive::Undefined)),
            },
            _ => false,
        })
        .collect();
    let rest_types: HashSet<_> = types_set
        .iter()
        .cloned()
        .filter(|ty| !matches!(ty.variant, Variant::Prim(_) | Variant::Lit(_)))
        .collect();

    let mut types: Vec<_> = prim_types
        .iter()
        .chain(lit_types.iter())
        .chain(rest_types.iter())
        .cloned()
        .collect();
    types.sort_by_key(|k| k.id);

    if types.len() > 1 {
        ctx.union(types)
    } else {
        types[0].clone()
    }
}