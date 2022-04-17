use itertools::Itertools;

use super::js_ast::*;

pub fn print_js(prog: &Program) -> String {
    prog.body
        .iter()
        .map(|child| print_statement(child, &0))
        .join("\n")
}

pub fn indent(level: &u32) -> String {
    let mut result: String = String::from("");
    for _ in 0..*level {
        result.push_str("    ");
    }
    result
}

pub fn print_statement(stmt: &Statement, level: &u32) -> String {
    match stmt {
        Statement::Decl { pattern, value } => {
            let pattern = print_pattern(pattern);
            let value = print_expr(value, level);
            format!("{}const {pattern} = {value};", indent(level))
        }
        Statement::Expression { expr } => {
            let expr = print_expr(expr, level);
            format!("{}{expr}", indent(level))
        }
        Statement::Return { arg } => {
            let arg = print_expr(arg, level);
            format!("{}return {arg};", indent(level))
        }
    }
}

pub fn print_pattern(pattern: &Pattern) -> String {
    match pattern {
        Pattern::Ident { name } => name.to_owned(),
    }
}

pub fn print_expr(expr: &Expression, level: &u32) -> String {
    match expr {
        Expression::Call { func, args } => {
            let wrap_func = match func.as_ref() {
                Expression::Function { .. } => true,
                _ => false,
            };

            let func = print_expr(func, level);
            let args = args.iter().map(|arg| print_expr(arg, level)).join(", ");

            if wrap_func {
                format!("({func})({args})")
            } else {
                format!("{func}({args})")
            }
        }
        Expression::Function { params, body } => {
            let params = params.iter().map(|param| print_param(param)).join(", ");
            let wrap = body.len() <= 1;
            let new_level = if wrap { *level } else { *level + 1 };
            let body = body
                .iter()
                .map(|child| print_statement(child, &new_level))
                .join("\n");
            if wrap {
                let body = body.trim_start();
                format!("({params}) => {body}")
            } else {
                format!("({params}) => {{\n{body}\n{}}}", indent(level))
            }
        }
        Expression::Ident { name } => name.to_owned(),
        Expression::Literal { literal } => format!("{literal}"),
        Expression::Binary { op, left, right } => {
            let wrap_right = match (expr, right.as_ref()) {
                (
                    Expression::Binary { op: parent_op, .. },
                    Expression::Binary { op: right_op, .. },
                ) => {
                    // Division and subtraction are not commutative operations so we
                    // need to have some additional logic to handle things like
                    // `a / (b / c)` and `a - (b - c)`.
                    match (parent_op, right_op) {
                        (BinaryOp::Div, BinaryOp::Div) => true,
                        (BinaryOp::Sub, BinaryOp::Sub) => true,
                        _ => get_precedence(right_op) < get_precedence(parent_op),
                    }
                }
                _ => false,
            };

            let wrap_left = match (expr, left.as_ref()) {
                (
                    Expression::Binary { op: parent_op, .. },
                    Expression::Binary { op: right_op, .. },
                ) => get_precedence(right_op) < get_precedence(parent_op),
                _ => false,
            };

            let left = if wrap_left {
                format!("({})", print_expr(left, level))
            } else {
                print_expr(left, level)
            };
            let right = if wrap_right {
                format!("({})", print_expr(right, level))
            } else {
                print_expr(right, level)
            };

            let op = match op {
                BinaryOp::Add => String::from("+"),
                BinaryOp::Sub => String::from("-"),
                BinaryOp::Mul => String::from("*"),
                BinaryOp::Div => String::from("/"),
                BinaryOp::Mod => String::from("%"),
                BinaryOp::Exp => String::from("**"),
            };

            format!("{} {} {}", left, op, right)
        }
        Expression::Unary { op, arg } => {
            let op = match op {
                UnaryOp::Neg => "=",
                UnaryOp::Not => "!",
            };
            let arg = print_expr(arg, level);
            format!("{op}{arg}")
        }
    }
}

pub fn print_param(param: &Param) -> String {
    match param {
        Param::Ident { name } => name.to_owned(),
        Param::Rest { name } => format!("...{name}"),
    }
}

fn get_precedence(op: &BinaryOp) -> i32 {
    match op {
        BinaryOp::Add => 1,
        BinaryOp::Sub => 1,
        BinaryOp::Mul => 2,
        BinaryOp::Div => 2,
        BinaryOp::Mod => 2,
        BinaryOp::Exp => 3,
    }
}