use crate::ast::ident::Ident;
use crate::ast::jsx::JSXElement;
use crate::ast::literal::Lit;
use crate::ast::pattern::Pattern;
use crate::ast::span::Span;
use crate::ast::types::{TypeAnn, TypeParam};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub body: Vec<Statement>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Comment {
    pub span: Span,
    pub text: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    VarDecl {
        span: Span,
        comments: Option<Vec<Comment>>,
        pattern: Pattern,
        init: Option<Expr>,
        declare: bool,
    },
    TypeDecl {
        span: Span,
        declare: bool,
        id: Ident,
        type_ann: TypeAnn,    
        type_params: Option<Vec<TypeParam>>,    
    },
    Expr {
        span: Span,
        expr: Expr,
    }, // NOTE: does not include Expr::Let
}

// #[derive(Debug, Clone, PartialEq, Eq)]
// struct Block {
//     pub span: Span,
//     pub stmts: Vec<Expr>,
// }

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct App {
    pub span: Span,
    pub lam: Box<Expr>,
    pub args: Vec<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fix {
    pub span: Span,
    pub expr: Box<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IfElse {
    pub span: Span,
    pub cond: Box<Expr>,
    pub consequent: Box<Expr>,
    pub alternate: Box<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lambda {
    pub span: Span,
    pub params: Vec<Pattern>,
    pub body: Box<Expr>,
    pub is_async: bool,
    pub return_type: Option<TypeAnn>,
    pub type_params: Option<Vec<TypeParam>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Let {
    pub span: Span,
    pub pattern: Option<Pattern>,
    pub init: Box<Expr>,
    pub body: Box<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Op {
    pub span: Span,
    pub op: BinOp,
    pub left: Box<Expr>,
    pub right: Box<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Obj {
    pub span: Span,
    pub props: Vec<Prop>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Prop {
    Shorthand(Ident),
    KeyValue(KeyValueProp),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeyValueProp {
    pub span: Span,
    pub name: String,
    pub value: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Await {
    pub span: Span,
    pub expr: Box<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Tuple {
    pub span: Span,
    pub elems: Vec<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Member {
    pub span: Span,
    pub obj: Box<Expr>,
    pub prop: MemberProp,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MemberProp {
    Ident(Ident),
    Computed(ComputedPropName),
}

impl MemberProp {
    pub fn name(&self) -> String {
        match self {
            MemberProp::Ident(Ident { name, .. }) => name.to_owned(),
            MemberProp::Computed(_) => todo!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComputedPropName {
    pub span: Span, // includes enclosing []
    pub expr: Box<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    App(App),
    Fix(Fix),
    Ident(Ident),
    IfElse(IfElse),
    JSXElement(JSXElement),
    Lambda(Lambda),
    Let(Let),
    Lit(Lit),
    Op(Op),
    Obj(Obj),
    Await(Await),
    Tuple(Tuple),
    Member(Member),
}

impl Expr {
    pub fn span(&self) -> Span {
        match &self {
            Expr::App(app) => app.span.to_owned(),
            Expr::Fix(fix) => fix.span.to_owned(),
            Expr::Ident(ident) => ident.span.to_owned(),
            Expr::IfElse(if_else) => if_else.span.to_owned(),
            Expr::JSXElement(elem) => elem.span.to_owned(),
            Expr::Lambda(lam) => lam.span.to_owned(),
            Expr::Let(r#let) => r#let.span.to_owned(),
            Expr::Lit(lit) => lit.span(),
            Expr::Op(op) => op.span.to_owned(),
            Expr::Obj(obj) => obj.span.to_owned(),
            Expr::Await(r#await) => r#await.span.to_owned(),
            Expr::Tuple(tuple) => tuple.span.to_owned(),
            Expr::Member(member) => member.span.to_owned(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    EqEq,
    NotEq,
    Gt,
    GtEq,
    Lt,
    LtEq,
}
