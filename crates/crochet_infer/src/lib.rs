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
        let ctx = Context::default();
        let expr = expr_parser().parse(input).unwrap();
        let scheme = infer::infer_expr(&ctx, &expr).unwrap();
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
    #[should_panic = "Property 'foo' missing in {x: 5, y: 10}"]
    fn missing_property_when_destructuring() {
        infer_prog("let {foo} = {x: 5, y: 10}");
    }

    #[test]
    fn obj_assignment() {
        let ctx = infer_prog("let p = {x: 5, y: 10}");

        assert_eq!(get_type("p", &ctx), "{x: 5, y: 10}");
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
    #[should_panic = "Property 'y' missing in {x: 5}"]
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
    #[should_panic = "Property 'c' missing in {a: string, b: boolean}"]
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
}