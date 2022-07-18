mod constraint_solver;
mod context;
pub mod infer;
mod infer_expr;
mod infer_lambda;
mod infer_mem;
mod infer_pattern;
mod infer_prog;
mod infer_type_ann;
mod substitutable;
pub mod types;
mod util;

pub use context::*;
pub use infer_expr::*;
pub use infer_prog::*;

#[cfg(test)]
mod tests {
    use chumsky::prelude::*;
    use crochet_parser::*;

    use super::*;

    fn infer(input: &str) -> String {
        let mut ctx = Context::default();
        let expr = expr_parser().parse(input).unwrap();
        let scheme = infer::infer_expr(&mut ctx, &expr).unwrap();
        println!("scheme = {:#?}", scheme);
        format!("{scheme}")
    }

    fn infer_prog(input: &str) -> Context {
        let prog = parser().parse(input).unwrap();
        infer::infer_prog(&prog).unwrap()
    }

    fn get_type(name: &str, ctx: &Context) -> String {
        let t = ctx.values.get(name).unwrap();
        format!("{t}")
    }

    #[test]
    fn infer_i_combinator() {
        let ctx = infer_prog("let I = (x) => x");
        assert_eq!(get_type("I", &ctx), "<t0>(t0) => t0");
    }

    #[test]
    fn infer_k_combinator() {
        let ctx = infer_prog("let K = (x) => (y) => x");
        assert_eq!(get_type("K", &ctx), "<t0, t1>(t0) => (t1) => t0");
    }

    #[test]
    fn infer_s_combinator() {
        let ctx = infer_prog("let S = (f) => (g) => (x) => f(x)(g(x))");
        assert_eq!(
            get_type("S", &ctx),
            "<t0, t1, t2>((t0) => (t1) => t2) => ((t0) => t1) => (t0) => t2"
        );
    }

    #[test]
    fn infer_skk() {
        let src = r#"
        let S = (f) => (g) => (x) => f(x)(g(x))
        let K = (x) => (y) => x
        let I = S(K)(K)
        "#;
        let ctx = infer_prog(src);
        assert_eq!(get_type("K", &ctx), "<t0, t1>(t0) => (t1) => t0");
        assert_eq!(
            get_type("S", &ctx),
            "<t0, t1, t2>((t0) => (t1) => t2) => ((t0) => t1) => (t0) => t2"
        );
        assert_eq!(get_type("I", &ctx), "<t0>(t0) => t0");
    }

    #[test]
    fn infer_adding_variables() {
        let src = r#"
        let x = 5
        let y = 10
        let z = x + y
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("z", &ctx), "number");
    }

    #[test]
    fn infer_if_else() {
        let src = r#"
        let n = 0
        let result = if n == 0 { 5 } else { 10 }
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("result", &ctx), "5 | 10");
    }

    #[test]
    fn infer_if() {
        let src = r#"
        let n = 0
        let result = if n == 0 { 5; }
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("result", &ctx), "undefined");
    }

    #[test]
    #[should_panic = "Consequent for 'if' without 'else' must not return a value"]
    fn infer_if_must_be_undefined() {
        let src = r#"
        let n = 0
        let result = if n == 0 { 5 }
        "#;
        infer_prog(src);
    }

    #[test]
    fn infer_fib() {
        let src = r###"
        let rec fib = (n) => if n == 0 {
            0
        } else if n == 1 {
            1
        } else {
            fib(n - 1) + fib(n - 2)
        }
        "###;
        let ctx = infer_prog(src);

        assert_eq!(get_type("fib", &ctx), "(number) => number");
    }

    #[test]
    fn infer_app_of_lam() {
        assert_eq!(infer("((x) => x)(5)"), "5");
    }

    #[test]
    fn inner_let() {
        assert_eq!(infer("() => {let x = 5; x}"), "() => 5");
    }

    #[test]
    fn inner_let_with_type_annotation() {
        assert_eq!(infer("() => {let x: number = 5; x}"), "() => number");
    }

    #[test]
    fn infer_tuple() {
        assert_eq!(infer("[5, true, \"hello\"]"), "[5, true, \"hello\"]");
    }

    #[test]
    fn basic_subtyping_assignment() {
        let ctx = infer_prog("let a: number = 5");

        assert_eq!(get_type("a", &ctx), "number");
    }

    #[test]
    fn infer_destructuring_tuple() {
        let src = r#"
        let [a, b, c] = [5, true, "hello"]
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("a", &ctx), "5");
        assert_eq!(get_type("b", &ctx), "true");
        assert_eq!(get_type("c", &ctx), "\"hello\"");
    }

    #[test]
    fn infer_destructuring_tuple_extra_init_elems() {
        let src = r#"
        let [a, b] = [5, true, "hello"]
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("a", &ctx), "5");
        assert_eq!(get_type("b", &ctx), "true");
    }

    #[test]
    #[should_panic = "Duplicate identifier in pattern"]
    fn infer_destructuring_tuple_reused_identifier() {
        let src = r#"
        let [a, a] = [5, true]
        "#;
        infer_prog(src);
    }

    #[test]
    fn infer_destructuring_nested_tuples() {
        let src = r#"
        let [[a, b], c] = [[5, true], "hello"]
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("a", &ctx), "5");
        assert_eq!(get_type("b", &ctx), "true");
        assert_eq!(get_type("c", &ctx), "\"hello\"");
    }

    #[test]
    fn infer_destructuring_function_params() {
        let result = infer("([x, y]) => x + y");

        assert_eq!(result, "([number, number]) => number");
    }

    #[test]
    fn infer_destructuring_function_params_with_type_annotations() {
        let result = infer("([x, y]: [string, boolean]) => [x, y]");

        assert_eq!(result, "([string, boolean]) => [string, boolean]");
    }

    #[test]
    fn infer_incomplete_destructuring_function_params_with_type_annotations() {
        let result = infer("([x]: [string, boolean]) => x");

        assert_eq!(result, "([string, boolean]) => string");
    }

    #[test]
    fn destructuring_tuple_inside_lambda() {
        let result = infer("(p) => {let [x, y] = p; x + y}");

        assert_eq!(result, "([number, number]) => number");
    }

    #[test]
    #[should_panic = "too many elements to unpack"]
    fn infer_destructuring_tuple_extra_init_elems_too_many_elements_to_unpack() {
        let src = r#"
        let [a, b, c, d] = [5, true, "hello"]
        "#;
        infer_prog(src);
    }

    #[test]
    fn infer_destructuring_tuple_with_type_annotation() {
        let src = r#"
        let [a, b, c]: [number, boolean, string] = [5, true, "hello"]
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("a", &ctx), "number");
        assert_eq!(get_type("b", &ctx), "boolean");
        assert_eq!(get_type("c", &ctx), "string");
    }

    #[test]
    #[should_panic = "Unification failure"]
    fn infer_destructuring_tuple_with_incorrect_type_annotation() {
        let src = r#"
        let [a, b, c]: [number, boolean, string] = [5, "hello", true]
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("a", &ctx), "number");
        assert_eq!(get_type("b", &ctx), "boolean");
        assert_eq!(get_type("c", &ctx), "string");
    }

    #[test]
    fn infer_destructuring_tuple_extra_init_elems_with_type_annotation() {
        let src = r#"
        let [a, b]: [number, boolean] = [5, true, "hello"]
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("a", &ctx), "number");
        assert_eq!(get_type("b", &ctx), "boolean");
    }

    #[test]
    #[should_panic = "too many elements to unpack"]
    fn infer_destructuring_tuple_extra_init_elems_too_many_elements_to_unpack_with_type_annotation()
    {
        let src = r#"
        let [a, b, c, d]: [number, boolean, string, number] = [5, true, "hello"]
        "#;
        infer_prog(src);
    }

    #[test]
    fn infer_obj() {
        assert_eq!(infer("{x:5, y: 10}"), "{x: 5, y: 10}");
    }

    #[test]
    fn infer_nested_obj() {
        assert_eq!(
            infer("{a: {b: {c: \"hello\"}}}"),
            "{a: {b: {c: \"hello\"}}}"
        );
    }

    #[test]
    fn destructure_obj() {
        let ctx = infer_prog("let {x, y} = {x: 5, y: 10}");

        assert_eq!(get_type("x", &ctx), "5");
        assert_eq!(get_type("y", &ctx), "10");
    }

    #[test]
    fn destructure_obj_with_optional() {
        let src = r#"
        declare let point: {x: number, y: number, z?: number}
        let {x, y, z} = point
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("z", &ctx), "number | undefined");
    }

    #[test]
    fn destructure_obj_with_renaming() {
        let src = "let {x: a, y: b} = {x: 5, y: 10}";
        let ctx = infer_prog(src);

        assert_eq!(get_type("a", &ctx), "5");
        assert_eq!(get_type("b", &ctx), "10");
        assert_eq!(ctx.values.get("x"), None);
        assert_eq!(ctx.values.get("y"), None);
    }

    #[test]
    #[should_panic = "Duplicate identifier in pattern"]
    fn infer_destructuring_obj_reused_identifier() {
        let src = "let {x: a, y: a} = {x: 5, y: 10}";
        infer_prog(src);
    }

    #[test]
    fn nested_destructure_obj() {
        let ctx = infer_prog("let {a: {b: {c}}} = {a: {b: {c: \"hello\"}}}");

        assert_eq!(ctx.values.get("a"), None);
        assert_eq!(ctx.values.get("b"), None);
        assert_eq!(get_type("c", &ctx), "\"hello\"");
    }

    #[test]
    fn partial_destructure_obj() {
        let ctx = infer_prog("let {x} = {x: 5, y: 10}");

        assert_eq!(get_type("x", &ctx), "5");
    }

    #[test]
    fn partial_destructure_disjoint_union_common_property() {
        let src = r#"
        declare let obj: {
            type: "foo",
            same: string,
            diff: boolean,
        } | {
            type: "bar",
            same: string,
            diff: number,
        }
        let {same, diff} = obj
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("same", &ctx), "string");
        assert_eq!(get_type("diff", &ctx), "boolean | number");
    }

    #[test]
    fn partial_destructure_disjoint_union_common_optional_property() {
        let src = r#"
        declare let obj: {type: "foo", value?: string} | {type: "bar", value?: number}
        let {value} = obj
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("value", &ctx), "string | number | undefined");
    }

    // TODO: In order for this to work, we need custom handling for unifying
    // a union of objects with an object.
    #[test]
    #[ignore]
    fn partial_destructure_disjoint_union_uncommon_property() {
        let src = r#"
        declare let obj: {type: "foo", value: string} | {type: "bar"}
        let {value} = obj
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("value", &ctx), "string | undefined");
    }

    #[test]
    #[should_panic = "Unification failure"]
    fn missing_property_when_destructuring() {
        infer_prog("let {foo} = {x: 5, y: 10}");
    }

    #[test]
    fn obj_assignment() {
        let ctx = infer_prog("let p = {x: 5, y: 10}");

        assert_eq!(get_type("p", &ctx), "{x: 5, y: 10}");
    }

    #[test]
    fn obj_assignment_shorthand() {
        let src = r#"
        let x = 5
        let y = 10
        let p = {x, y}
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("p", &ctx), "{x: 5, y: 10}");
    }

    #[test]
    #[should_panic]
    fn obj_assignment_shorthand_missing_variable() {
        let src = r#"
        let x = 5
        let p = {x, y}
        "#;

        infer_prog(src);
    }

    #[test]
    fn obj_assignment_with_type_annotation() {
        let ctx = infer_prog("let p: {x: number, y: number} = {x: 5, y: 10}");

        assert_eq!(get_type("p", &ctx), "{x: number, y: number}");
    }

    #[test]
    fn obj_assignment_with_type_annotation_extra_properties() {
        let ctx = infer_prog("let p: {x: number, y: number} = {x: 5, y: 10, z: 15}");

        assert_eq!(get_type("p", &ctx), "{x: number, y: number}");
    }

    #[test]
    #[should_panic = "Unification failure"]
    fn obj_assignment_with_type_annotation_missing_properties() {
        infer_prog("let p: {x: number, y: number} = {x: 5}");
    }

    #[test]
    fn obj_param_destructuring() {
        assert_eq!(
            infer("({x, y}) => x + y"),
            "({x: number, y: number}) => number"
        );
    }

    #[test]
    fn obj_param_destructuring_with_type_annotation() {
        assert_eq!(
            infer("({x, y}: {x: 5, y: 10}) => x + y"),
            "({x: 5, y: 10}) => number"
        );
    }

    #[test]
    fn obj_param_partial_destructuring_with_type_annotation() {
        assert_eq!(
            infer("({a}: {a: string, b: boolean}) => a"),
            "({a: string, b: boolean}) => string"
        );
    }

    #[test]
    #[should_panic = "Unification failure"]
    fn obj_destructuring_with_type_annotation_missing_param() {
        infer("({c}: {a: string, b: boolean}) => c");
    }

    #[test]
    fn destructuring_inside_lambda() {
        assert_eq!(
            infer("(p) => {let {x, y} = p; x + y}"),
            "({x: number, y: number}) => number"
        );
    }

    #[test]
    fn infer_if_let() {
        let src = r#"
        let p = {x: 5, y: 10}
        let sum = if let {x, y} = p {
            x + y
        } else {
            0
        }
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("sum", &ctx), "number");

        // Ensures we aren't polluting the outside context
        assert!(ctx.values.get("x").is_none());
        assert!(ctx.values.get("y").is_none());
    }

    #[test]
    fn infer_if_let_without_else_no_return() {
        let src = r#"
        let p = {x: 5, y: 10}
        if let {x, y} = p {
            x + y;
        }
        "#;

        infer_prog(src);
    }

    #[test]
    #[should_panic = "Consequent for 'if' without 'else' must not return a value"]
    fn infer_if_let_without_else_errors_with_return() {
        let src = r#"
        let p = {x: 5, y: 10}
        if let {x, y} = p {
            x + y
        }
        "#;

        infer_prog(src);
    }

    #[test]
    fn infer_if_let_chaining() {
        let src = r#"
        let p = {x: 5, y: 10}
        let c = {a: 0, b: 1}
        let sum = if let {x, y} = p {
            x
        } else if let {a, b} = c {
            b
        } else {
            0
        }
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("sum", &ctx), "5 | 1 | 0");

        // Ensures we aren't polluting the outside context
        assert!(ctx.values.get("x").is_none());
        assert!(ctx.values.get("y").is_none());
    }

    #[test]
    fn infer_if_let_inside_lambda() {
        let src = r#"
        let add = (p) => {
            if let {x, y} = p {
                x + y
            } else {
                0
            }
        }        
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("add", &ctx), "({x: number, y: number}) => number");
    }

    #[test]
    fn infer_if_let_refutable_is() {
        let src = r#"
        declare let a: string | number
        let sum = if let x is number = a {
            x + 5
        } else {
            0
        }
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("sum", &ctx), "number");

        // Ensures we aren't polluting the outside context
        assert!(ctx.values.get("x").is_none());
    }

    #[test]
    fn infer_if_let_refutable_is_with_unreachable_code() {
        let src = r#"
        declare let a: string | number
        let result = if let x is number = a {
            x + 5
        } else if let y is string = a {
            y
        } else {
            true
        }
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("result", &ctx), "number | string | true");

        // Ensures we aren't polluting the outside context
        assert!(ctx.values.get("x").is_none());
        assert!(ctx.values.get("y").is_none());
    }

    #[test]
    #[should_panic = "Unification failure"]
    fn infer_if_let_refutable_is_unification_failure() {
        let src = r#"
        declare let a: string | number
        let sum = if let x is string = a {
            x + 5
        }
        "#;

        infer_prog(src);
    }

    #[test]
    fn infer_if_let_refutable_is_inside_obj() {
        let src = r#"
        declare let foo: {bar: string | number}
        let sum = if let {bar: x is number} = foo {
            x + 5
        } else {
            0
        }
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("sum", &ctx), "number");

        // Ensures we aren't polluting the outside context
        assert!(ctx.values.get("x").is_none());
    }

    #[test]
    #[should_panic = "Unification failure"]
    fn infer_if_let_refutable_is_inside_obj_incorrect_type() {
        let src = r#"
        declare let foo: {bar: string}
        let result = if let {bar: x is number} = foo {
            x
        } else {
            0
        }
        "#;

        infer_prog(src);
    }

    // TODO: figure out what to do when there are multiple matches... it should be the same
    // thing that happens when destructuring a union of objects (or union of tuples).
    #[test]
    fn infer_if_let_disjoint_union() {
        let src = r#"
        declare let action: {type: "foo", num: number} | {type: "bar", str: string}
        let result = if let {type: "foo", num} = action {
            num + 5
        } else {
            0
        }
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("result", &ctx), "number");

        // Ensures we aren't polluting the outside context
        assert!(ctx.values.get("x").is_none());
    }

    #[test]
    fn infer_if_let_disjoint_union_chaining() {
        let src = r#"
        declare let action: {type: "foo", num: number} | {type: "bar", str: string}
        let result = if let {type: "foo", num} = action {
            num + 5
        } else if let {type: "bar", str} = action {
            str
        } else {
            true
        }
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("result", &ctx), "string | number | true");

        // Ensures we aren't polluting the outside context
        assert!(ctx.values.get("x").is_none());
    }

    #[test]
    #[should_panic = "Unification failure"]
    fn infer_if_let_disjoint_union_no_matches() {
        let src = r#"
        declare let action: {type: "foo", num: number} | {type: "bar", str: string}
        let result = if let {type: "bar", num} = action {
            num
        } else {
            0
        }
        "#;

        infer_prog(src);
    }

    #[test]
    #[should_panic = "Unification failure"]
    fn infer_if_let_disjoint_union_incorrect_match() {
        let src = r#"
        declare let action: {type: "foo", num: number} | {type: "bar", str: string}
        let result = if let {type: "bar", str} = action {
            str + 5
        } else {
            0
        }
        "#;

        infer_prog(src);
    }

    #[test]
    fn infer_if_let_refutable_is_inside_array() {
        let src = r#"
        declare let point: [string | number, string | number]
        let result = if let [x is number, y is number] = point {
            x + y
        } else {
            0
        }
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("result", &ctx), "number");

        // Ensures we aren't polluting the outside context
        assert!(ctx.values.get("x").is_none());
        assert!(ctx.values.get("y").is_none());
    }

    // TODO: handle refutable patterns in if-else
    // TODO: handle irrefutable patterns with union types
    // e.g. given the following type:
    // foo: {a: number, b: number} | {x: string, y: string}
    // or
    // bar: {a: number, b: number} | {a: string, a: string}
    // if we do:
    // if let {a, b} = foo { ... }
    // a and b will both be numbers
    // if let {a, b} = bar { ... }
    // a and b will both be number | string

    #[test]
    fn infer_let_ignore_result() {
        assert_eq!(infer("() => {let _ = 5; 10}"), "() => 10");
    }

    #[test]
    fn infer_expression_statements() {
        assert_eq!(infer("() => {5; 10}"), "() => 10");
    }

    #[test]
    fn type_decl() {
        let src = r#"
        type Point = {x: number, y: number}
        let p: Point = {x: 5, y: 10}
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("p", &ctx), "Point");
    }

    #[test]
    fn external_decl() {
        let src = r#"
        type Point = {x: number, y: number}
        declare let p: Point
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("p", &ctx), "Point");
    }

    #[test]
    fn lambda_with_type_param() {
        let src = r#"
        let fst = <T>(a: T, b: T): T => {
            a
        }
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("fst", &ctx), "<t0>(t0, t0) => t0");
    }

    #[test]
    fn lambda_with_multiple_type_params() {
        let src = r#"
        let fst = <A, B>(a: A, b: B): A => {
            a
        }
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("fst", &ctx), "<t0, t1>(t0, t1) => t0");
    }

    #[test]
    fn calling_a_generic_function() {
        let src = r#"
        let fst = <A, B>(a: A, b: B): A => {
            a
        }
        let result = fst(5, 10)
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("result", &ctx), "5");
    }

    #[test]
    fn calling_lambda_returning_generic_lambda() {
        let src = r#"
        let run = () => (a, b) => a
        let fst = run()
        let x = fst(5, 10)
        let y = fst(true, false)
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("fst", &ctx), "<t0, t1>(t0, t1) => t0");
        assert_eq!(get_type("x", &ctx), "5");
        assert_eq!(get_type("y", &ctx), "true");
    }

    #[test]
    fn calling_generic_lambda_inside_lambda() {
        let src = r#"
        let run = () => {
            let fst = (a, b) => a;
            [fst(5, 10), fst(true, false)]
        }
        let result = run()
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("result", &ctx), "[5, true]");
    }

    #[test]
    fn lambda_with_explicit_types() {
        let src = r#"
        let add = (a: number, b: number): number => {
            a + b
        }
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("add", &ctx), "(number, number) => number");
    }

    #[test]
    #[should_panic = "Unification failure"]
    fn lambda_with_incorrect_return_type() {
        let src = r#"
        let add = (a: number, b: number): string => {
            a + b
        }
        "#;

        infer_prog(src);
    }

    // TODO: make this test case return an error
    #[test]
    #[should_panic = "Unification failure"]
    fn lambda_with_incorrect_param_type() {
        let src = r#"
        let add = (a: number, b: string): number => {
            a + b
        }
        "#;

        infer_prog(src);
    }

    #[test]
    fn call_lam_with_subtypes() {
        let src = r#"
        declare let add: (number, number) => number
        let sum = add(5, 10)
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("sum", &ctx), "number");
    }

    #[test]
    #[should_panic = "Unification failure"]
    fn call_lam_with_wrong_types() {
        let src = r#"
        declare let add: (number, number) => number
        let sum = add("hello", true)
        "#;

        infer_prog(src);
    }

    #[test]
    fn call_lam_with_extra_params() {
        let src = r#"
        declare let add: (number, number) => number
        let sum = add(5, 10, "hello")
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("sum", &ctx), "number");
    }

    #[test]
    fn call_lam_with_too_few_params_result_in_partial_application() {
        let src = r#"
        declare let add: (number, number) => number
        let add5 = add(5)
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("add5", &ctx), "(number) => number");
    }

    #[test]
    fn call_lam_with_too_few_params_result_in_partial_application_no_params() {
        let src = r#"
        declare let add: (number, number) => number
        let plus = add()
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("plus", &ctx), "(number, number) => number");
    }

    #[test]
    fn call_lam_multiple_times_with_too_few_params() {
        let src = r#"
        declare let add: (number, number) => number
        let sum = add(5)(10)
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("sum", &ctx), "number");
    }

    #[test]
    fn pass_callback_with_too_few_params() {
        let src = r#"
        declare let fold_num: ((number, number) => boolean, number) => number
        let result = fold_num((x) => true, 0)
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("result", &ctx), "number");
    }

    #[test]
    fn pass_callback_whose_params_are_supertypes_of_expected_callback() {
        let src = r#"
        declare let fold_num: ((5, 10) => boolean, number) => number
        let result = fold_num((x: number, y: number) => true, 0)
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("result", &ctx), "number");
    }

    #[test]
    #[should_panic = "Couldn't unify lambdas"]
    fn pass_callback_with_too_many_params() {
        // This is not allowed because `fold_num` can't provide all of the params
        // that the callback is expecting and it would result in partial application
        // when the `fold_num` is not expecting it.  While it's possible to conceive
        // of a scenario where a callback returns a function and a partially applied
        // calback results in correct function, allowing this in the type checker
        // is bound to result in confusing and hard to understand code.
        let src = r#"
        declare let fold_num: ((number, number) => boolean, number) => number
        let result = fold_num((x, y, z) => true, 0)
        "#;

        infer_prog(src);
    }

    // TODO: TypeScript takes the union of the params when unifying them
    #[test]
    #[ignore]
    fn call_generic_lam_with_subtypes() {
        let src = r#"
        declare let add: <T>(T, T) => T
        let sum = add(5, 10)
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("sum", &ctx), "5 | 10");
    }

    #[test]
    fn infer_generic_lam() {
        // TODO: figure out how to handle parametric functions like this
        let src = r#"
        let add = <T>(x: T, y: T): T => {
            x + y
        }
        let sum = add(5, 5)
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("add", &ctx), "(number, number) => number");
        assert_eq!(get_type("sum", &ctx), "number");
    }

    #[test]
    fn infer_member_access() {
        let src = r#"
        let p = {x: 5, y: 10}
        let x = p.x
        let y = p.y
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("x", &ctx), "5");
        assert_eq!(get_type("y", &ctx), "10");
    }

    #[test]
    fn infer_optional_member() {
        let src = r#"
        declare let obj: {a: string, b?: number}
        let a = obj.a
        let b = obj.b
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("a", &ctx), "string");
        assert_eq!(get_type("b", &ctx), "number | undefined");
    }

    #[test]
    fn infer_nested_member_access() {
        let src = r#"
        let obj = {a: {b: {c: "hello"}}}
        let c = obj.a.b.c
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("c", &ctx), "\"hello\"");
    }

    #[test]
    fn infer_calling_method_on_obj() {
        let src = r#"
        let obj = {add: (a, b) => a + b}
        let sum = obj.add(5, 10)
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("sum", &ctx), "number");
    }

    #[test]
    fn infer_combined_member_acces_and_method_call_result() {
        let src = r#"
        type Point = {x: number, y: number}
        let obj = {add: (p: Point, q: Point) => {
            let result = {x: p.x + q.x, y: p.y + q.y};
            result
        }}
        let p = {x: 5, y: 10}
        let q = {x: 0, y: 1}
        let sum_x = obj.add(p, q).x
        "#;

        let ctx = infer_prog(src);

        assert_eq!(get_type("sum_x", &ctx), "number");
    }

    #[test]
    #[should_panic = "Record literal doesn't contain property"]
    fn infer_missing_member() {
        let src = r#"
        let p = {x: 5, y: 10}
        let z = p.z
        "#;

        infer_prog(src);
    }

    #[test]
    fn infer_obj_type_from_use() {
        let src = r#"
        let mag = (p) => p.x * p.x + p.y * p.y
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("mag", &ctx), "({x: number, y: number}) => number");
    }

    #[test]
    fn infer_obj_type_from_use_with_more_properties() {
        let src = r#"
        let mag = (p) => p.x + p.y + p.z
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("mag", &ctx), "({x: number, y: number, z: number}) => number");
    }

    #[test]
    fn infer_obj_type_based_on_nested_member_access() {
        let src = r#"let slope = (line) => (line.p1.y - line.p0.y) / (line.p1.x - line.p0.x)"#;
        let ctx = infer_prog(src);

        assert_eq!(
            get_type("slope", &ctx),
            "({p1: {x: number, y: number}, p0: {x: number, y: number}}) => number"
        );
    }

    #[test]
    fn destructure_obj_with_rest() {
        let src = r#"
        declare let point: {x: number, y: number, z?: number}
        let {z, ...rest} = point
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("rest", &ctx), "{x: number, y: number}");
    }

    #[test]
    #[should_panic = "Only one rest is allowed in an object pattern"]
    fn destructure_obj_with_rest_undecidable() {
        let src = r#"
        declare let point: {x: number, y: number, z?: number}
        let {z, ...p, ...q} = point
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("q", &ctx), "{x: number, y: number}");
    }

    #[test]
    fn spread_an_object() {
        let src = r#"
        declare let point: {x: number, y: number}
        let point_3d = {...point, z: 15}
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("point_3d", &ctx), "{x: number, y: number, z: 15}");
    }

    #[test]
    fn spread_multiple_objects_no_overlap() {
        let src = r#"
        let foo = {a: true, b: "hello"}
        let bar = {x: 5, y: 10}
        let obj = {...foo, ...bar}
        "#;
        let ctx = infer_prog(src);

        assert_eq!(
            get_type("obj", &ctx),
            "{a: true, b: \"hello\", x: 5, y: 10}"
        );
    }

    #[test]
    fn spread_multiple_objects_with_overlap() {
        let src = r#"
        let foo = {a: true, b: "hello"}
        let bar = {b: 5, c: false}
        let obj = {...foo, ...bar}
        "#;
        let ctx = infer_prog(src);

        assert_eq!(
            get_type("obj", &ctx),
            "{a: true, b: \"hello\" & 5, c: false}"
        );
    }

    #[test]
    fn infer_obj_from_spread() {
        let src = r#"
        type Point = {x: number, y: number, z: number}
        declare let mag: (Point) => number
        let mag_2d = (p) => {
            mag({...p, z: 0})
        }
        "#;
        let ctx = infer_prog(src);

        assert_eq!(
            get_type("mag_2d", &ctx),
            "({x: number, y: number}) => number"
        );
    }

    #[test]
    #[should_panic = "Unification is undecidable"]
    fn infer_obj_from_spread_undecidable() {
        let src = r#"
        type Point = {x: number, y: number, z: number}
        declare let mag: (Point) => number
        let mag_2d = (p, q) => {
            mag({...p, ...q, z: 0})
        }
        "#;
        infer_prog(src);
    }

    #[test]
    fn call_overloaded_function() {
        let src = r#"
        declare let add: ((number, number) => number) & ((string, string) => string)
        let str = add("hello", "world")
        let num = add(5, 10)
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("str", &ctx), "string");
        assert_eq!(get_type("num", &ctx), "number");
    }

    #[test]
    #[should_panic = "Couldn't unify lambda with intersection"]
    fn call_overloaded_function_with_wrong_params() {
        let src = r#"
        declare let add: ((number, number) => number) & ((string, string) => string)
        add("hello", 10)
        "#;

        infer_prog(src);
    }

    #[test]
    fn async_await() {
        let src = r#"
        let add_async = async (a, b) => {
            await a + await b
        }
        "#;
        let ctx = infer_prog(src);

        assert_eq!(
            get_type("add_async", &ctx),
            "(Promise<number>, Promise<number>) => Promise<number>"
        );
    }

    #[test]
    fn async_doesnt_rewrap_return_promise() {
        let src = r#"
        let passthrough = async (x: Promise<string>) => x
        "#;
        let ctx = infer_prog(src);

        assert_eq!(
            get_type("passthrough", &ctx),
            "(Promise<string>) => Promise<string>"
        );
    }

    #[test]
    #[should_panic = "Can't use `await` inside non-async lambda"]
    fn await_only_works_in_async_functions() {
        let src = r#"
        let add_async = (a, b) => {
            await a + await b
        }
        "#;

        infer_prog(src);
    }

    #[test]
    #[should_panic = "Can't use `await` inside non-async lambda"]
    fn await_only_works_in_async_functions_nested() {
        let src = r#"
        let add_async = async (a, b) => {
            let inner = (x, y) => {
                await x + await y
            };
            await inner(a, b)
        }
        "#;

        infer_prog(src);
    }

    #[test]
    fn await_works_in_nested_async_functions() {
        let src = r#"
        let add_async = async (a, b) => {
            let inner = async (x, y) => {
                await x + await y
            };
            await inner(a, b)
        }
        "#;
        let ctx = infer_prog(src);

        assert_eq!(
            get_type("add_async", &ctx),
            "(Promise<number>, Promise<number>) => Promise<number>"
        );
    }

    #[test]
    fn jsx_element() {
        let src = r#"
        let elem = <div>Hello, world!</div>
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("elem", &ctx), "JSXElement");
    }

    #[test]
    fn jsx_custom_element() {
        let src = r#"
        let Foo = () => <div>Hello, world!</div>
        let elem = <Foo />
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("elem", &ctx), "JSXElement");
    }

    #[test]
    fn jsx_custom_element_with_props() {
        let src = r#"
        type Props = {msg: string}
        let Foo = (props: Props) => <div>{props.msg}</div>
        let elem = <Foo msg="Hello, world!" />
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("elem", &ctx), "JSXElement");
    }

    // TODO: disallow extra props
    #[test]
    fn jsx_custom_element_with_extra_props() {
        let src = r#"
        type Props = {msg: string}
        let Foo = (props: Props) => <div>{props.msg}</div>
        let elem = <Foo msg="Hello, world!" bar={true} />
        "#;
        let ctx = infer_prog(src);

        assert_eq!(get_type("elem", &ctx), "JSXElement");
    }

    #[test]
    #[should_panic = "Unification failure"]
    fn jsx_custom_element_with_incorrect_props() {
        let src = r#"
        type Props = {msg: string}
        let Foo = (props: Props) => <div>{props.msg}</div>
        let elem = <Foo msg={5} />
        "#;

        infer_prog(src);
    }

    #[test]
    #[should_panic = "Unification failure"]
    fn jsx_custom_element_with_missing_prop() {
        let src = r#"
        type Props = {msg: string}
        let Foo = (props: Props) => <div>{props.msg}</div>
        let elem = <Foo />
        "#;

        infer_prog(src);
    }

    #[test]
    #[should_panic = "Component 'Bar' is not in scope"]
    fn jsx_custom_element_not_found() {
        let src = r#"
        let Foo = () => <div>Hello, world!</div>
        let elem = <Bar />
        "#;

        infer_prog(src);
    }

    #[test]
    #[should_panic = "Component must be a function"]
    fn jsx_custom_element_not_a_function() {
        let src = r#"
        let Foo = "hello, world"
        let elem = <Foo />
        "#;

        infer_prog(src);
    }

    #[test]
    #[should_panic = "Unification failure"]
    fn jsx_custom_element_incorrect_return() {
        let src = r#"
        let Foo = () => {x: 5, y: 10}
        let elem = <Foo />
        "#;

        infer_prog(src);
    }
}
