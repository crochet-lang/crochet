use chumsky::prelude::*;

use super::expr::expr_parser;
use super::pattern::pattern_parser;
use super::type_params::type_params;
use super::types::type_parser;
use super::util::just_with_padding;

use crate::ast::*;

pub fn decl_parser() -> impl Parser<char, Statement, Error = Simple<char>> {
    let comment = just("//")
        .ignore_then(take_until(just('\n')))
        .padded()
        .map_with_span(|(chars, _), span| {
            Comment {
                span,
                text: chars.into_iter().collect(),
            }
        });

    // We use `just` instead of `just_with_padding` here to ensure that
    // the span doesn't include leading whitespace.
    let pattern = pattern_parser();
    let var_decl_with_init = comment.repeated()
        .then(just("declare").or_not())
        .then_ignore(just_with_padding("let"))
        .then(just_with_padding("rec").or_not())
        .then(pattern.clone())
        .then_ignore(just_with_padding("="))
        .then(expr_parser())
        .map_with_span(
            |((((comments, declare), rec), pattern), init), span: Span| -> Statement {
                let comments = match comments.len() {
                    0 => None,
                    _ => Some(comments)
                };

                match rec {
                    Some(_) => {
                        // `let fib = fix((fib) => (n) => ...)`
                        // TODO: Fix always wraps a lambda
                        let fix = Expr::Fix(Fix {
                            span: init.span(),
                            expr: Box::from(Expr::Lambda(Lambda {
                                span: init.span(),
                                params: vec![pattern.clone()],
                                body: Box::from(init),
                                is_async: false,
                                return_type: None,
                                type_params: None, // TODO: support type params on VarDecls
                            })),
                        });

                        Statement::VarDecl {
                            span,
                            comments,
                            pattern,
                            init: Some(fix),
                            declare: declare.is_some(),
                        }
                    }
                    None => Statement::VarDecl {
                        span,
                        comments,
                        pattern,
                        init: Some(init),
                        declare: declare.is_some(),
                    },
                }
            },
        );

    let var_decl = comment.repeated()
        .then(just("declare").or_not())
        .then_ignore(just_with_padding("let"))
        .then(pattern_parser())
        .map_with_span(|((comments, declare), pattern), span: Span| -> Statement {
            let comments = match comments.len() {
                0 => None,
                _ => Some(comments)
            };
            
            Statement::VarDecl {
                span,
                comments,
                pattern,
                init: None,
                declare: declare.is_some(),
            }
        });

    choice((type_decl(), var_decl_with_init, var_decl))
}

fn type_decl() -> impl Parser<char, Statement, Error = Simple<char>> {
    let type_ann = type_parser();
    let ident = text::ident().map_with_span(|name, span: Span| Ident { name, span });

    let type_decl = just("declare")
        .or_not()
        .then_ignore(just_with_padding("type"))
        .then(ident)
        .then(type_params(type_ann.clone().boxed()).or_not())
        .then(just_with_padding("=").ignore_then(type_ann))
        .map_with_span(
            |(((declare, id), type_params), type_ann), span| Statement::TypeDecl {
                span,
                declare: declare.is_some(),
                id,
                type_ann,
                type_params,
            },
        );

    type_decl
}
