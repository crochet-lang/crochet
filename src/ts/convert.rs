use super::super::syntax::{BindingIdent, Expr};
use super::super::types::{Scheme, TLam, Type, TypeKind};
use super::ast::{Param, TsQualifiedType, TsType};

/// Converts a Scheme to a TsQualifiedTyepe for eventual export to .d.ts.
pub fn convert_scheme(scheme: &Scheme, expr: Option<&Expr>) -> TsQualifiedType {
    TsQualifiedType {
        ty: convert_type(&scheme.ty, expr),
        type_params: scheme.qualifiers.clone(),
    }
}

/// Converts an internal Type to a TsType for eventual export to .d.ts.
///
/// `expr` should be the original expression that `ty` was inferred
/// from if it exists.
pub fn convert_type(ty: &Type, expr: Option<&Expr>) -> TsType {
    match &ty.kind {
        TypeKind::Var => {
            let chars: Vec<_> = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz".chars().collect();
            let id = chars.get(ty.id.to_owned() as usize).unwrap();
            TsType::Var(format!("{id}"))
        },
        TypeKind::Prim(prim) => TsType::Prim(prim.to_owned()),
        TypeKind::Lit(lit) => TsType::Lit(lit.to_owned()),
        // This is used to copy the names of args from the expression
        // over to the lambda's type.
        TypeKind::Lam(TLam { args, ret }) => {
            match expr {
                // TODO: handle is_async
                Some(Expr::Lam {
                    args: expr_args, ..
                }) => {
                    if args.len() != expr_args.len() {
                        panic!("number of args don't match")
                    } else {
                        let params: Vec<_> = args
                            .iter()
                            .zip(expr_args)
                            .map(|(arg, (binding, _span))| {
                                let name = match binding {
                                    BindingIdent::Ident { name } => name,
                                    BindingIdent::Rest { name } => name,
                                };
                                Param {
                                    name: name.to_owned(),
                                    ty: convert_type(arg, None),
                                }
                            })
                            .collect();

                        TsType::Func {
                            params,
                            ret: Box::new(convert_type(&ret, None)),
                        }
                    }
                },
                // Fix nodes are assumed to wrap a lambda where the body of
                // the lambda is recursive function.
                Some(Expr::Fix { expr }) => {
                    match expr.as_ref() {
                        (Expr::Lam {body, ..}, _) => {
                            convert_type(ty, Some(&body.0))
                        },
                        _ => panic!("mismatch")
                    }
                },
                None => {
                    let params: Vec<_> = args
                        .iter()
                        .enumerate()
                        .map(|(i, arg)| Param {
                            name: format!("arg{}", i),
                            ty: convert_type(arg, None),
                        })
                        .collect();
                    TsType::Func {
                        params,
                        ret: Box::new(convert_type(&ret, None)),
                    }
                },
                _ => panic!("mismatch"),
            }
        }
        TypeKind::Union(types) => TsType::Union(types.iter().map(|ty| convert_type(ty, None)).collect()),
    }
}