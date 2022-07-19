use std::collections::HashMap;

use crochet_ast::*;

use crate::substitutable::{Subst, Substitutable};

use super::context::{lookup_alias, Context, Env};
use super::infer_type_ann::*;
use super::types::{self, freeze_scheme, Scheme, Type, Variant};
use super::unify::unify;
use super::util::*;

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
    let result = match expr {
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
            let t = ret_type.apply(&s);

            // return (s3 `compose` s2 `compose` s1, apply s3 tv)
            Ok((s, t))
        }
        Expr::Fix(Fix { expr, .. }) => {
            let (s1, t) = infer(ctx, expr)?;
            let tv = ctx.fresh_var();
            let s2 = unify(&ctx.lam(vec![tv.clone()], Box::from(tv.clone())), &t, ctx)?;
            Ok((compose_subs(&s2, &s1), tv.apply(&s2)))
        }
        Expr::Ident(Ident { name, .. }) => {
            let s = Subst::default();
            let t = ctx.lookup_value(name)?;
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
                                        }
                                        JSXAttrValue::JSXExprContainer(JSXExprContainer {
                                            expr,
                                            ..
                                        }) => infer(ctx, expr)?,
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
                            Prop::Shorthand(Ident { name, .. }) => {
                                let t = ctx.lookup_value(name)?;
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

            Ok((s, t))
        }
        Expr::Empty(_) => {
            let t = ctx.prim(Primitive::Undefined);
            let s = Subst::default();
            Ok((s, t))
        }
    };

    let (s, t) = result?;

    // TODO: apply `s` to `ctx.values`
    for (k, v) in ctx.values.clone() {
        ctx.values.insert(k.to_owned(), v.apply(&s));
    }

    Ok((s, t))
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
                None => Err(String::from("Record literal doesn't contain property")),
            }
        }
        Variant::Alias(alias) => {
            let t = lookup_alias(ctx, alias)?;
            infer_property_type(&t, prop, ctx)
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
