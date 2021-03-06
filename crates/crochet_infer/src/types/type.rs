use itertools::join;
use std::fmt;
use std::hash::Hash;

use crate::Context;
use crate::types::{Lit, Primitive};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TProp {
    pub name: String,
    pub optional: bool,
    pub ty: Type,
}

impl TProp {
    pub fn get_type(&self, ctx: &Context) -> Type {
        match self.optional {
            true => ctx.union(vec![self.ty.to_owned(), ctx.prim(Primitive::Undefined)]),
            false => self.ty.to_owned(),
        }
    }
}

impl fmt::Display for TProp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Self { name, optional, ty } = self;
        match optional {
            false => write!(f, "{name}: {ty}"),
            true => write!(f, "{name}?: {ty}"),
        }
    }
}

#[derive(Clone, Debug, Eq)]
pub struct VarType {
    pub id: i32,
    pub frozen: bool,
}

impl PartialEq for VarType {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Hash for VarType {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

#[derive(Clone, Debug, Eq)]
pub struct LamType {
    pub params: Vec<Type>, // TOOD: rename this params
    pub ret: Box<Type>,
    pub is_call: bool,
}

impl PartialEq for LamType {
    fn eq(&self, other: &Self) -> bool {
        self.params == other.params && self.ret == other.ret
    }
}

impl Hash for LamType {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.params.hash(state);
        self.ret.hash(state);
    }
}

#[derive(Clone, Debug, Eq)]
pub struct AliasType {
    pub name: String,
    pub type_params: Option<Vec<Type>>,
}

impl PartialEq for AliasType {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.type_params == other.type_params
    }
}

impl Hash for AliasType {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.type_params.hash(state);
    }
}

#[derive(Clone, Debug, Eq)]
pub struct MemberType {
    pub obj: Box<Type>,
    pub prop: String, // TODO: allow numbers as well for accessing elements on tuples and arrays
}

impl PartialEq for MemberType {
    fn eq(&self, other: &Self) -> bool {
        self.obj == other.obj && self.prop == other.prop
    }
}

impl Hash for MemberType {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.obj.hash(state);
        self.prop.hash(state);
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Variant {
    Var,
    Lam(LamType),
    Prim(Primitive),
    Lit(Lit),
    Union(Vec<Type>),
    Intersection(Vec<Type>),
    Object(Vec<TProp>),
    Alias(AliasType),
    Tuple(Vec<Type>),
    Array(Box<Type>),
    Rest(Box<Type>),
    Member(MemberType),
}

#[derive(Clone, Debug, Eq)]
pub struct Type {
    pub variant: Variant,
    pub id: i32,
    pub frozen: bool,
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match &self.variant {
            Variant::Var => self.id == other.id,
            _ => self.variant == other.variant,
        }
    }
}

impl Hash for Type {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match &self.variant {
            Variant::Var => self.id.hash(state),
            _ => self.variant.hash(state),
        }
    }
}

impl fmt::Display for Type {
    // TODO: add in parentheses where necessary to get the precedence right
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.variant {
            Variant::Var => {
                let id = self.id;
                write!(f, "t{id}")
            }
            Variant::Lam(LamType { params, ret, .. }) => {
                write!(f, "({}) => {}", join(params, ", "), ret)
            }
            Variant::Prim(prim) => write!(f, "{}", prim),
            Variant::Lit(lit) => write!(f, "{}", lit),
            Variant::Union(types) => write!(f, "{}", join(types, " | ")),
            Variant::Intersection(types) => {
                write!(f, "{}", join(types, " & "))
            }
            Variant::Object(props) => write!(f, "{{{}}}", join(props, ", ")),
            Variant::Alias(AliasType {
                name, type_params, ..
            }) => match type_params {
                Some(params) => write!(f, "{name}<{}>", join(params, ", ")),
                None => write!(f, "{name}"),
            },
            Variant::Tuple(types) => write!(f, "[{}]", join(types, ", ")),
            Variant::Array(t) => write!(f, "{t}[]"),
            Variant::Rest(arg) => write!(f, "...{arg}"),
            Variant::Member(MemberType { obj, prop, .. }) => write!(f, "{obj}[\"{prop}\"]"),
        }
    }
}

fn set_frozen(ty: Type, frozen: bool) -> Type {
    let variant = match ty.variant {
        Variant::Var => Variant::Var,
        Variant::Lam(lam) => Variant::Lam(LamType {
            is_call: lam.is_call,
            params: lam.params.into_iter().map(freeze).collect(),
            ret: Box::from(freeze(lam.ret.as_ref().clone())),
        }),
        Variant::Prim(prim) => Variant::Prim(prim),
        Variant::Lit(lit) => Variant::Lit(lit),
        Variant::Union(types) => Variant::Union(types.into_iter().map(freeze).collect()),
        Variant::Intersection(types) => {
            Variant::Intersection(types.into_iter().map(freeze).collect())
        }
        Variant::Object(props) => Variant::Object(
            props
                .into_iter()
                .map(|prop| TProp {
                    ty: freeze(prop.ty),
                    ..prop
                })
                .collect(),
        ),
        Variant::Alias(alias) => Variant::Alias(AliasType {
            name: alias.name,
            type_params: alias
                .type_params
                .map(|type_params| type_params.into_iter().map(freeze).collect()),
        }),
        Variant::Tuple(types) => Variant::Tuple(types.into_iter().map(freeze).collect()),
        Variant::Array(t) => Variant::Array(Box::from(freeze(t.as_ref().clone()))),
        Variant::Rest(arg) => Variant::Rest(Box::from(freeze(arg.as_ref().clone()))),
        Variant::Member(member) => Variant::Member(MemberType {
            obj: Box::from(freeze(member.obj.as_ref().clone())),
            prop: member.prop,
        }),
    };
    Type {
        variant,
        frozen,
        ..ty
    }
}

pub fn freeze(ty: Type) -> Type {
    set_frozen(ty, true)
}

pub fn unfreeze(ty: Type) -> Type {
    set_frozen(ty, false)
}
