use std::collections::{HashMap, HashSet};

use crochet_ast::*;

use crate::substitutable::Substitutable;

use super::context::{Context, Env};
use super::infer_type_ann::*;
use super::substitutable::Subst;
use super::types::{self, freeze_scheme, Scheme, Type, Variant, Flag};
use super::util::{generalize, normalize, simplify_intersection};

pub fn infer_prog(prog: &Program) -> Result<Context, String> {
    let mut ctx: Context = Context::default();
    // TODO: replace with Class type once it exists
    // We use {_name: "Promise"} to differentiate it from other
    // object types.
    let promise_scheme = Scheme::from(ctx.object(vec![types::TProp {
        name: String::from("_name"),
        optional: false,
        ty: ctx.lit(Lit::str(String::from("Promise"), 0..0)),
    }]));
    ctx.types.insert(String::from("Promise"), promise_scheme);
    // TODO: replace with Class type once it exists
    // We use {_name: "JSXElement"} to differentiate it from other
    // object types.
    let jsx_element_scheme = Scheme::from(ctx.object(vec![types::TProp {
        name: String::from("_name"),
        optional: false,
        ty: ctx.lit(Lit::str(String::from("JSXElement"), 0..0)),
    }]));
    ctx.types
        .insert(String::from("JSXElement"), jsx_element_scheme);

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
                        // An initial value should always be used when using a normal
                        // `let` statement
                        let init = init.as_ref().unwrap();

                        let (pa, s) =
                            infer_pattern_and_init(pattern, init, &mut ctx, &PatternUsage::Assign)?;

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
                infer_expr(&mut ctx, expr)?;
            }
        };
    }

    Ok(ctx)
}

pub fn infer_expr(ctx: &mut Context, expr: &Expr) -> Result<Scheme, String> {
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

enum PatternUsage {
    Assign,
    Match,
}

fn infer_pattern_and_init(
    pat: &Pattern,
    init: &Expr,
    ctx: &mut Context,
    pu: &PatternUsage,
) -> Result<(Assump, Subst), String> {
    let type_param_map = HashMap::new();
    let (ps, pa, pt) = infer_pattern(pat, ctx, &type_param_map)?;

    let (is, it) = infer(ctx, init)?;

    // Unifies initializer and pattern.
    let s = match pu {
        // Assign: The inferred type of the init value must be a sub-type
        // of the pattern it's being assigned to.
        PatternUsage::Assign => unify(&it, &pt, ctx)?,
        // Matching: The pattern must be a sub-type of the expression
        // it's being matched against
        PatternUsage::Match => unify(&pt, &it, ctx)?,
    };

    // infer_pattern can generate a non-empty Subst when the pattern includes
    // a type annotation.
    let s = compose_many_subs(&[is, ps, s]);

    Ok((pa.apply(&s), s))
}

fn infer_let(
    pat: &Pattern,
    init: &Expr,
    body: &Expr,
    ctx: &Context,
    pu: &PatternUsage,
) -> Result<(Subst, Type), String> {
    let mut new_ctx = ctx.clone();
    let (pa, s1) = infer_pattern_and_init(pat, init, &mut new_ctx, pu)?;

    // Inserts the new variables from infer_pattern() into the
    // current context.
    for (name, scheme) in pa {
        new_ctx.values.insert(name.to_owned(), scheme.to_owned());
    }

    let (s2, t2) = infer(&mut new_ctx, body)?;

    // Copies over the count from new_ctx so that it's unique across Contexts.
    ctx.state.count.set(new_ctx.state.count.get());

    let s = compose_subs(&s2, &s1);
    let t = t2;
    Ok((s, t))
}

fn is_promise(ty: &Type) -> bool {
    matches!(&ty.variant, Variant::Alias(types::AliasType { name, .. }) if name == "Promise")
}

fn infer(ctx: &mut Context, expr: &Expr) -> Result<(Subst, Type), String> {
    match expr {
        Expr::App(App { lam, args, .. }) => {
            let (s1, lam_type) = infer(ctx, lam)?;
            let (mut args_ss, args_ts): (Vec<_>, Vec<_>) =
                args.iter().filter_map(|arg| infer(ctx, arg).ok()).unzip();

            let ret_type = ctx.fresh_var();
            // Are we missing an `apply()` call here?
            // Maybe, I could see us needing an apply to handle generic functions properly
            // s3       <- unify (apply s2 t1) (TArr t2 tv)
            let call_type = Type {
                id: ctx.fresh_id(),
                frozen: false,
                variant: Variant::Lam(types::LamType {
                    params: args_ts,
                    ret: Box::from(ret_type.clone()),
                    is_call: true,
                }),
                flag: None,
            };
            let s3 = unify(&call_type, &lam_type, ctx)?;

            // ss = [s3, ...args_ss, s1]
            let mut ss = vec![s3];
            ss.append(&mut args_ss);
            ss.push(s1);

            let s = compose_many_subs(&ss);

            Ok((s.clone(), ret_type.apply(&s)))
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
                match cond.as_ref() {
                    Expr::LetExpr(LetExpr { pat, expr, .. }) => {
                        // TODO: warn if the pattern isn't refutable
                        let (s1, t1) = infer_let(pat, expr, consequent, ctx, &PatternUsage::Match)?;
                        let (s2, t2) = infer(ctx, alternate)?;

                        let s = compose_many_subs(&[s1, s2]);
                        let t = union_types(&t1, &t2, ctx);
                        Ok((s, t))
                    }
                    _ => {
                        let (s1, t1) = infer(ctx, cond)?;
                        let (s2, t2) = infer(ctx, consequent)?;
                        let (s3, t3) = infer(ctx, alternate)?;
                        let s4 = unify(&t1, &ctx.prim(Primitive::Bool), ctx)?;

                        let s = compose_many_subs(&[s1, s2, s3, s4]);
                        let t = union_types(&t2, &t3, ctx);
                        Ok((s, t))
                    }
                }
            }
            None => match cond.as_ref() {
                Expr::LetExpr(LetExpr { pat, expr, .. }) => {
                    let (s1, t1) = infer_let(pat, expr, consequent, ctx, &PatternUsage::Match)?;
                    let s2 = match unify(&t1, &ctx.prim(Primitive::Undefined), ctx) {
                        Ok(s) => Ok(s),
                        Err(_) => Err(String::from(
                            "Consequent for 'if' without 'else' must not return a value",
                        )),
                    }?;

                    let s = compose_subs(&s2, &s1);
                    let t = t1;
                    Ok((s, t))
                }
                _ => {
                    let (s1, t1) = infer(ctx, cond)?;
                    let (s2, t2) = infer(ctx, consequent)?;
                    let s3 = unify(&t1, &ctx.prim(Primitive::Bool), ctx)?;
                    let s4 = match unify(&t2, &ctx.prim(Primitive::Undefined), ctx) {
                        Ok(s) => Ok(s),
                        Err(_) => Err(String::from(
                            "Consequent for 'if' without 'else' must not return a value",
                        )),
                    }?;

                    let s = compose_many_subs(&[s1, s2, s3, s4]);
                    let t = t2;
                    Ok((s, t))
                }
            },
        },
        Expr::JSXElement(JSXElement {
            name,
            attrs,
            children: _,
            ..
        }) => {
            let first_char = name.chars().next().unwrap();
            // JSXElement's starting with an uppercase char are user defined.
            if first_char.is_uppercase() {
                match ctx.values.get(name) {
                    Some(scheme) => {
                        let ct = ctx.instantiate(scheme);
                        match &ct.variant {
                            Variant::Lam(_) => {
                                let mut ss: Vec<_> = vec![];
                                let mut props: Vec<_> = vec![];
                                for attr in attrs {
                                    let (s, t) = match &attr.value {
                                        JSXAttrValue::Lit(lit) => {
                                            infer(ctx, &Expr::Lit(lit.to_owned()))?
                                        },
                                        JSXAttrValue::JSXExprContainer(JSXExprContainer {expr, ..}) => {
                                            infer(ctx, expr)?
                                        },
                                    };
                                    ss.push(s);

                                    let prop = types::TProp {
                                        name: attr.ident.name.to_owned(),
                                        optional: false,
                                        ty: t,
                                    };
                                    props.push(prop);
                                }

                                let ret_type = ctx.alias("JSXElement", None);

                                let call_type = Type {
                                    id: ctx.fresh_id(),
                                    frozen: false,
                                    variant: Variant::Lam(types::LamType {
                                        params: vec![ctx.object(props)],
                                        ret: Box::from(ret_type.clone()),
                                        is_call: true,
                                    }),
                                    flag: None,
                                };

                                let s1 = compose_many_subs(&ss);
                                let s2 = unify(&call_type, &ct, ctx)?;

                                let s = compose_subs(&s2, &s1);

                                return Ok((s, ret_type));
                            }
                            _ => return Err(String::from("Component must be a function")),
                        }
                    }
                    None => return Err(format!("Component '{name}' is not in scope")),
                }
            }

            let s = Subst::default();
            // TODO: check props on JSXInstrinsics
            let t = ctx.alias("JSXElement", None);

            Ok((s, t))
        }
        Expr::Lambda(Lambda {
            params,
            body,
            is_async,
            return_type: rt_type_ann,
            type_params,
            ..
        }) => {
            let mut new_ctx = ctx.clone();
            new_ctx.is_async = is_async.to_owned();

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
                    let (ps, pa, pt) = infer_pattern(param, &new_ctx, &type_params_map)?;

                    // Inserts any new variables introduced by infer_pattern() into
                    // the current context.
                    for (name, scheme) in pa {
                        new_ctx.values.insert(name, scheme);
                    }

                    Ok((ps, pt))
                })
                .collect();

            let (ss, ts): (Vec<_>, Vec<_>) = params?.iter().cloned().unzip();

            let (rs, rt) = infer(&mut new_ctx, body)?;

            // Copies over the count from new_ctx so that it's unique across Contexts.
            ctx.state.count.set(new_ctx.state.count.get());

            let rt = if *is_async && !is_promise(&rt) {
                ctx.alias("Promise", Some(vec![rt]))
            } else {
                rt
            };

            let s = match rt_type_ann {
                Some(rt_type_ann) => unify(
                    &rt,
                    &infer_type_ann_with_params(rt_type_ann, ctx, &type_params_map),
                    ctx,
                )?,
                None => Subst::default(),
            };
            let t = ctx.lam(ts, Box::from(rt));
            let s = compose_subs(&s, &compose_subs(&rs, &compose_many_subs(&ss)));
            let t = t.apply(&s);

            Ok((s, t))
        }
        Expr::Let(Let {
            pattern,
            init,
            body,
            ..
        }) => {
            match pattern {
                Some(pat) => infer_let(pat, init, body, ctx, &PatternUsage::Assign),
                None => {
                    // TODO: warn about unused values
                    infer(ctx, body)
                }
            }
        }
        Expr::LetExpr(_) => {
            panic!("Unexpected LetExpr.  All LetExprs should be handled by IfElse arm.")
        }
        Expr::Lit(lit) => {
            let s = Subst::new();
            let t = ctx.lit(lit.to_owned());
            Ok((s, t))
        }
        Expr::Op(Op {
            op, left, right, ..
        }) => {
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
        Expr::Obj(Obj { props, .. }) => {
            let mut ss: Vec<Subst> = vec![];
            let mut ps: Vec<types::TProp> = vec![];
            let mut spread_types: Vec<_> = vec![];
            for p in props {
                match p {
                    PropOrSpread::Prop(p) => {
                        match p.as_ref() {
                            Prop::Shorthand(Ident {name, ..}) => {
                                let t = ctx.lookup_value(name);
                                ps.push(ctx.prop(name, t, false));
                            }
                            Prop::KeyValue(KeyValueProp { name, value, .. }) => {
                                let (s, t) = infer(ctx, value)?;
                                ss.push(s);
                                // TODO: check if the inferred type is T | undefined and use that
                                // determine the value of optional
                                ps.push(ctx.prop(name, t, false));
                            }
                        }
                    }
                    PropOrSpread::Spread(SpreadElement { expr, .. }) => {
                        let (s, t) = infer(ctx, expr)?;
                        ss.push(s);
                        spread_types.push(t);
                    }
                }
            }

            let s = compose_many_subs(&ss);
            if spread_types.is_empty() {
                let t = ctx.object(ps);
                Ok((s, t))
            } else {
                let mut all_types = spread_types;
                all_types.push(ctx.object(ps));
                let t = simplify_intersection(&all_types, ctx);
                Ok((s, t))
            }
        }
        Expr::Await(Await { expr, .. }) => {
            if !ctx.is_async {
                return Err(String::from("Can't use `await` inside non-async lambda"));
            }

            let (s1, t1) = infer(ctx, expr)?;
            let wrapped_type = ctx.fresh_var();
            let promise_type = ctx.alias("Promise", Some(vec![wrapped_type.clone()]));

            let s2 = unify(&t1, &promise_type, ctx)?;

            let s = compose_subs(&s2, &s1);

            Ok((s, wrapped_type))
        }
        Expr::Tuple(Tuple { elems, .. }) => {
            let result: Result<Vec<(Subst, Type)>, String> =
                elems.iter().map(|elem| infer(ctx, elem)).collect();
            let (ss, ts): (Vec<_>, Vec<_>) = result?.iter().cloned().unzip();

            let s = compose_many_subs(&ss);
            let t = ctx.tuple(ts);
            Ok((s, t))
        }
        Expr::Member(Member { obj, prop, .. }) => {
            let (obj_s, obj_t) = infer(ctx, obj)?;
            let (prop_s, prop_t) = infer_property_type(&obj_t, prop, ctx)?;

            let s = compose_subs(&prop_s, &obj_s);
            let t = unwrap_member_type(&prop_t, ctx);

            // TODO: implement Substitutable for Env and use that
            if let Expr::Ident(ident) = obj.as_ref() {
                let obj = obj_t.apply(&s);
                ctx.values.insert(ident.name.to_owned(), Scheme::from(obj));
            }

            Ok((s, t))
        }
        Expr::Empty(_) => {
            let t = ctx.prim(Primitive::Undefined);
            let s = Subst::default();
            Ok((s, t))
        }
    }
}

fn lookup_alias(ctx: &Context, name: &str) -> Result<Type, String> {
    match ctx.types.get(name) {
        // TODO: handle schemes with qualifiers
        Some(scheme) => Ok(scheme.ty.to_owned()),
        None => Err(String::from("Can't find alias '{name}' in context")),
    }
}

fn infer_property_type(
    obj_t: &Type,
    prop: &MemberProp,
    ctx: &Context,
) -> Result<(Subst, Type), String> {
    match &obj_t.variant {
        Variant::Object(props) => {
            let mem_t = ctx.mem(obj_t.clone(), &prop.name());
            match props.iter().find(|p| p.name == prop.name()) {
                Some(_) => Ok((Subst::default(), mem_t)),
                None => {
                    if obj_t.flag == Some(Flag::MemberAccess) {
                        // TODO:
                        // - create a new object type from the existing one and add the missing property
                        // - create a Subst manually that maps 
                        let mut props = props.to_owned();
                        let tv = ctx.fresh_var();
                        props.push(types::TProp {
                            name: prop.name(),
                            // We assume the property is not optional when inferring an
                            // object from a member access.
                            optional: false,
                            ty: tv.clone(),
                        });
                        let obj = ctx.object_with_flag(props, Flag::MemberAccess);

                        let s = Subst::from([(obj_t.id, obj)]);
                        let t = tv;

                        Ok((s, t))
                    } else {
                        Err(String::from("Record literal doesn't contain property"))
                    }                    
                },
            }
        }
        Variant::Alias(types::AliasType { name, .. }) => {
            let t = lookup_alias(ctx, name)?;
            infer_property_type(&t, prop, ctx)
        }
        Variant::Var => {
            let tv = ctx.fresh_var();
            let obj = ctx.object_with_flag(
                vec![types::TProp {
                    name: prop.name(),
                    // We assume the property is not optional when inferring an
                    // object from a member access.
                    optional: false,
                    ty: tv.clone(),
                }],
                Flag::MemberAccess,
            );
            let mem1 = ctx.mem(obj_t.clone(), &prop.name());
            let mem2 = ctx.mem(obj.clone(), &prop.name());

            let s1 = unify(&mem1, &mem2, ctx)?;
            let s2 = unify(obj_t, &obj, ctx)?;

            let s = compose_subs(&s2, &s1);
            let t = tv;

            Ok((s, t))
        }
        _ => todo!("Unhandled {obj_t} in infer_property_type"),
    }
}

fn unwrap_member_type(t: &Type, ctx: &Context) -> Type {
    if let Variant::Member(member) = &t.variant {
        if let Variant::Object(props) = &member.obj.as_ref().variant {
            let prop = props.iter().find(|prop| prop.name == member.prop);
            if let Some(prop) = prop {
                return prop.get_type(ctx);
            }
        }
    }
    t.to_owned()
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
        Ok(Subst::from([(id.to_owned(), t.to_owned())]))
    }
}

fn occurs_check(id: &i32, t: &Type) -> bool {
    t.ftv().contains(id)
}

fn compose_subs(s2: &Subst, s1: &Subst) -> Subst {
    let mut result: Subst = s1.iter().map(|(id, tv)| (*id, tv.apply(s2))).collect();
    result.extend(s2.to_owned());
    result
}

// subs are composed from left to right with ones to the right
// being applied to all of the ones to the left.
fn compose_many_subs(subs: &[Subst]) -> Subst {
    subs.iter()
        .fold(Subst::new(), |accum, next| compose_subs(&accum, next))
}

// If are multiple entries for the same type variable, this function merges
// them into a union type (simplifying the type if possible).
fn compose_subs_with_context(s1: &Subst, s2: &Subst, ctx: &Context) -> Subst {
    let mut result: Subst = s2.iter().map(|(i, t)| (*i, t.apply(s1))).collect();
    for (i, t) in s1 {
        match result.get(i) {
            Some(t1) => {
                let t = union_types(t, t1, ctx);
                result.insert(*i, t)
            }
            None => result.insert(*i, t.to_owned()),
        };
    }
    result
}

fn compose_many_subs_with_context(subs: &[Subst], ctx: &Context) -> Subst {
    subs.iter().fold(Subst::new(), |accum, next| {
        compose_subs_with_context(&accum, next, ctx)
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
            // Allowing type_ann_ty to be a subtype of pat_type because
            // only non-refutable patterns can have type annotations.
            let s = unify(&type_ann_ty, &pat_type, ctx)?;

            // Substs are applied to any new variables introduced.  This handles
            // the situation where explicit types have be provided for function
            // parameters.
            Ok((s.clone(), new_vars.apply(&s), type_ann_ty))
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
                            // TODO: handle default values

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
                            if rest_opt_ty.is_some() {
                                // TODO: return an Err() instead of panicking.
                                panic!("Maximum one rest pattern allowed in object patterns")
                            }
                            // TypeScript doesn't support spreading/rest in types so instead we
                            // do the following conversion:
                            // {x, y, ...rest} -> {x: A, y: B} & C
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

// Returns Ok(substitions) if t2 admits all values from t1 and an Err() otherwise.
fn unify(t1: &Type, t2: &Type, ctx: &Context) -> Result<Subst, String> {
    let result = match (&t1.variant, &t2.variant) {
        (Variant::Lit(lit), Variant::Prim(prim)) => {
            let b = matches!(
                (lit, prim),
                (types::Lit::Num(_), Primitive::Num)
                    | (types::Lit::Str(_), Primitive::Str)
                    | (types::Lit::Bool(_), Primitive::Bool)
            );
            if b {
                Ok(Subst::default())
            } else {
                Err(String::from("Unification failure"))
            }
        }
        (Variant::Lam(lam1), Variant::Lam(lam2)) => {
            let mut s = Subst::new();
            // If `lam1` is a function call then we treat it differently.  Instead
            // of checking if it's a subtype of `lam2`, we instead either:
            if lam1.is_call {
                if lam1.params.len() < lam2.params.len() {
                    // Partially application.
                    // If there is fewer than expected by `lam2` we return an new
                    // lambda that accepts the remaining params and returns the
                    // original return type.
                    let partial_ret =
                        ctx.lam(lam2.params[lam1.params.len()..].to_vec(), lam2.ret.clone());
                    for (p1, p2) in lam1.params.iter().zip(&lam2.params) {
                        // Each argument must be a subtype of the corresponding param.
                        let arg = p1.apply(&s);
                        let param = p2.apply(&s);
                        let s1 = unify(&arg, &param, ctx)?;
                        s = compose_subs(&s, &s1);
                    }
                    let s1 = unify(&lam1.ret.apply(&s), &partial_ret, ctx)?;
                    Ok(compose_subs(&s, &s1))
                } else {
                    // Regular application.
                    // Any extra params (args) that `lam1` has are ignored.
                    for (p1, p2) in lam1.params.iter().zip(&lam2.params) {
                        // Each argument must be a subtype of the corresponding param.
                        let arg = p1.apply(&s);
                        let param = p2.apply(&s);
                        let s1 = unify(&arg, &param, ctx)?;
                        s = compose_subs(&s, &s1);
                    }
                    let s1 = unify(&lam1.ret.apply(&s), &lam2.ret.apply(&s), ctx)?;
                    Ok(compose_subs(&s, &s1))
                }
            } else if lam1.params.len() <= lam2.params.len() {
                // If `lam1` isn't being applied then it's okay if has fewer params
                // than `lam2`.  This is because functions can be passed extra params
                // meaning that any place `lam2` is used, `lam1` can be used as well.
                for (p1, p2) in lam1.params.iter().zip(&lam2.params) {
                    // NOTE: The order of params is reverse.  This allows a callback
                    // whose params can accept more values (are supertypes) than the
                    // function will pass to the callback.
                    let s1 = unify(&p2.apply(&s), &p1.apply(&s), ctx)?;
                    s = compose_subs(&s, &s1);
                }
                let s1 = unify(&lam1.ret.apply(&s), &lam2.ret.apply(&s), ctx)?;
                Ok(compose_subs(&s, &s1))
            } else {
                Err(String::from("Couldn't unify lambdas"))
            }
        }
        (Variant::Lam(_), Variant::Intersection(types)) => {
            for t in types {
                let result = unify(t1, t, ctx);
                if result.is_ok() {
                    return result;
                }
            }
            Err(String::from("Couldn't unify lambda with intersection"))
        }
        (Variant::Object(props1), Variant::Object(props2)) => {
            // It's okay if t1 has extra properties, but it has to have all of t2's properties.
            let result: Result<Vec<_>, String> = props2
                .iter()
                .map(|prop2| {
                    let mut b = false;
                    let mut ss = vec![];
                    for prop1 in props1.iter() {
                        if prop1.name == prop2.name {
                            if let Ok(s) = unify(&prop1.get_type(ctx), &prop2.get_type(ctx), ctx) {
                                b = true;
                                ss.push(s);
                            }
                        }
                    }

                    match b {
                        true => Ok(compose_many_subs(&ss)),
                        false => Err(String::from("Unification failure")),
                    }
                })
                .collect();

            let ss = result?;
            Ok(compose_many_subs(&ss))
        }
        (Variant::Member(mem1), Variant::Member(mem2)) => {
            // NOTE: In order to infer object types from their usage we need to
            // be able to apply substitutions generated from inferring on Expr::Member
            // when inferring another Expr::Member that may occur quite far away from
            // the first one.
            assert_eq!(mem1.prop, mem2.prop);
            unify(&mem1.obj, &mem2.obj, ctx)
        }
        (Variant::Tuple(types1), Variant::Tuple(types2)) => {
            // It's okay if t1 has extra properties, but it has to have all of t2's properties.
            if types1.len() < types2.len() {
                // TODO: tweak this error message to include the types
                return Err(String::from("too many elements to unpack"));
            }
            let result: Result<Vec<_>, _> = types1
                .iter()
                .zip(types2.iter())
                .map(|(t1, t2)| unify(t1, t2, ctx))
                .collect();
            let ss = result?; // This is only okay if all calls to is_subtype are okay
            Ok(compose_many_subs(&ss))
        }
        (Variant::Union(types), _) => {
            let result: Result<Vec<_>, _> = types.iter().map(|t1| unify(t1, t2, ctx)).collect();
            let ss = result?; // This is only okay if all calls to is_subtype are okay
            Ok(compose_many_subs_with_context(&ss, ctx))
        }
        (_, Variant::Union(types)) => {
            let mut b = false;
            let mut ss = vec![];
            for t2 in types.iter() {
                if let Ok(s) = unify(t1, t2, ctx) {
                    b = true;
                    ss.push(s);
                }
            }

            match b {
                true => Ok(compose_many_subs(&ss)),
                false => Err(String::from("Unification failure")),
            }
        }
        (Variant::Var, _) => bind(&t1.id, t2),
        (_, Variant::Var) => bind(&t2.id, t1),
        (Variant::Object(props), Variant::Intersection(types)) => {
            let obj_types: Vec<_> = types
                .iter()
                .filter(|t| matches!(t.variant, Variant::Object(_)))
                .cloned()
                .collect();
            let rest_types: Vec<_> = types
                .iter()
                .filter(|t| matches!(t.variant, Variant::Var))
                .cloned()
                .collect();
            // TODO: check for other variants, if there are we should error

            let obj_type = simplify_intersection(&obj_types, ctx);

            println!("rest_types.len() = {}", rest_types.len());

            match rest_types.len() {
                0 => unify(t1, &obj_type, ctx),
                1 => {
                    let all_obj_props = match &obj_type.variant {
                        Variant::Object(props) => props.to_owned(),
                        _ => vec![],
                    };

                    let (obj_props, rest_props): (Vec<_>, Vec<_>) = props
                        .iter()
                        .cloned()
                        .partition(|p| all_obj_props.iter().any(|op| op.name == p.name));

                    let s1 = unify(&ctx.object(obj_props), &obj_type, ctx)?;

                    let rest_type = rest_types.get(0).unwrap();
                    let s2 = unify(&ctx.object(rest_props), rest_type, ctx)?;

                    let s = compose_subs(&s2, &s1);
                    Ok(s)
                }
                _ => Err(String::from("Unification is undecidable")),
            }
        }
        (Variant::Intersection(types), Variant::Object(props)) => {
            let obj_types: Vec<_> = types
                .iter()
                .filter(|t| matches!(t.variant, Variant::Object(_)))
                .cloned()
                .collect();
            let rest_types: Vec<_> = types
                .iter()
                .filter(|t| matches!(t.variant, Variant::Var))
                .cloned()
                .collect();
            // TODO: check for other variants, if there are we should error

            let obj_type = simplify_intersection(&obj_types, ctx);

            match rest_types.len() {
                0 => unify(&obj_type, t2, ctx),
                1 => {
                    let all_obj_props = match &obj_type.variant {
                        Variant::Object(props) => props.to_owned(),
                        _ => vec![],
                    };

                    let (obj_props, rest_props): (Vec<_>, Vec<_>) = props
                        .iter()
                        .cloned()
                        .partition(|p| all_obj_props.iter().any(|op| op.name == p.name));

                    let s_obj = unify(&obj_type, &ctx.object(obj_props), ctx)?;

                    let rest_type = rest_types.get(0).unwrap();
                    let s_rest = unify(rest_type, &ctx.object(rest_props), ctx)?;

                    let s = compose_subs(&s_rest, &s_obj);
                    Ok(s)
                }
                _ => Err(String::from("Unification is undecidable")),
            }
        }
        (Variant::Alias(alias1), Variant::Alias(alias2)) => {
            if alias1.name == alias2.name {
                match (&alias1.type_params, &alias2.type_params) {
                    (Some(tp1), Some(tp2)) => {
                        let result: Result<Vec<_>, _> = tp1
                            .iter()
                            .zip(tp2.iter())
                            .map(|(t1, t2)| unify(t1, t2, ctx))
                            .collect();
                        let ss = result?; // This is only okay if all calls to is_subtype are okay
                        Ok(compose_many_subs_with_context(&ss, ctx))
                    },
                    (None, None) => {
                        Ok(Subst::default())
                    },
                    _ => Err(String::from("Alias type mismatch"))
                }
            } else {
                todo!("unify(): handle aliases that point to another alias")
            }
        }
        (_, Variant::Alias(types::AliasType { name, .. })) => {
            let alias_t = lookup_alias(ctx, name)?;
            unify(t1, &alias_t, ctx)
        }
        (Variant::Alias(types::AliasType { name, .. }), _) => {
            let alias_t = lookup_alias(ctx, name)?;
            unify(&alias_t, t2, ctx)
        }
        (v1, v2) => {
            if v1 == v2 {
                Ok(Subst::new())
            } else {
                Err(String::from("Unification failure"))
            }
        }
    };
    if result.is_err() {
        println!("Can't unify t1 = {t1:#?} with t2 = {t2:#?}");
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    fn num(val: &str) -> Lit {
        Lit::num(val.to_owned(), 0..0)
    }

    fn str(val: &str) -> Lit {
        Lit::str(val.to_owned(), 0..0)
    }

    fn bool(val: &bool) -> Lit {
        Lit::bool(val.to_owned(), 0..0)
    }

    #[test]
    fn literals_are_subtypes_of_corresponding_primitives() {
        let ctx = Context::default();

        let result = unify(&ctx.lit(num("5")), &ctx.prim(Primitive::Num), &ctx);
        assert_eq!(result, Ok(Subst::default()));

        let result = unify(&ctx.lit(str("hello")), &ctx.prim(Primitive::Str), &ctx);
        assert_eq!(result, Ok(Subst::default()));

        let result = unify(&ctx.lit(bool(&true)), &ctx.prim(Primitive::Bool), &ctx);
        assert_eq!(result, Ok(Subst::default()));
    }

    #[test]
    fn object_subtypes() {
        let ctx = Context::default();

        let t1 = ctx.object(vec![
            types::TProp {
                name: String::from("foo"),
                optional: false,
                ty: ctx.lit(num("5")),
            },
            types::TProp {
                name: String::from("bar"),
                optional: false,
                ty: ctx.lit(bool(&true)),
            },
            // Having extra properties is okay
            types::TProp {
                name: String::from("baz"),
                optional: false,
                ty: ctx.prim(Primitive::Str),
            },
            // It's okay for qux to not appear in the subtype since
            // it's an optional property.
        ]);
        let t2 = ctx.object(vec![
            types::TProp {
                name: String::from("foo"),
                optional: false,
                ty: ctx.prim(Primitive::Num),
            },
            types::TProp {
                name: String::from("bar"),
                optional: true,
                ty: ctx.prim(Primitive::Bool),
            },
            types::TProp {
                name: String::from("qux"),
                optional: true,
                ty: ctx.prim(Primitive::Str),
            },
        ]);

        let result = unify(&t1, &t2, &ctx);
        assert_eq!(result, Err(String::from("Unification failure")));
    }

    // TODO: object subtype failure cases

    #[test]
    fn failure_case() {
        let ctx = Context::default();

        let result = unify(&ctx.prim(Primitive::Num), &ctx.lit(num("5")), &ctx);

        assert_eq!(result, Err(String::from("Unification failure")))
    }
}
