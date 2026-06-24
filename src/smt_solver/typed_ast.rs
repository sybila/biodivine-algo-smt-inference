use anyhow::anyhow;
use biodivine_lib_param_bn::{BinaryOp, FnUpdate, VariableId};
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::{SortKind, Symbol};

/// Analogous to [`SortKind`] but only admits types that are currently supported
/// by our solver implementations.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum AstType {
    Int,
    Bool,
}

impl Display for AstType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            AstType::Int => write!(f, "Int"),
            AstType::Bool => write!(f, "Bool"),
        }
    }
}

impl From<AstType> for SortKind {
    fn from(value: AstType) -> Self {
        match value {
            AstType::Bool => SortKind::Bool,
            AstType::Int => SortKind::Int,
        }
    }
}

impl TryFrom<SortKind> for AstType {
    type Error = anyhow::Error;

    fn try_from(value: SortKind) -> Result<Self, Self::Error> {
        match value {
            SortKind::Bool => Ok(AstType::Bool),
            SortKind::Int => Ok(AstType::Int),
            _ => Err(anyhow!(
                "Expected `Int` or `Bool`, but `{:?}` was given.",
                value
            )),
        }
    }
}

impl AstType {
    /// Create a named [`TypedAst`] constant using the Z3 sort corresponding to this [`AstType`].
    pub fn new_const<S: Into<Symbol>>(&self, name: S) -> TypedAst {
        match self {
            AstType::Int => Int::new_const(name).into(),
            AstType::Bool => Bool::new_const(name).into(),
        }
    }

    pub fn new_value(&self, value: u32) -> TypedAst {
        match self {
            AstType::Int => Int::from_u64(u64::from(value)).into(),
            AstType::Bool => Bool::from_bool(value > 0).into(),
        }
    }

    pub fn new_fresh_const(&self, prefix: &str) -> TypedAst {
        match self {
            AstType::Int => Int::fresh_const(prefix).into(),
            AstType::Bool => Bool::fresh_const(prefix).into(),
        }
    }
}

/// An enum wrapper for the supported AST kinds.
///
/// Technically, we could achieve similar behavior using methods that are already available
/// for the [`Dynamic`] AST node, but this makes it slightly more idiomatic in Rust.
#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub enum TypedAst {
    Int(Int),
    Bool(Bool),
}

impl TryFrom<Dynamic> for TypedAst {
    type Error = anyhow::Error;

    fn try_from(value: Dynamic) -> Result<Self, Self::Error> {
        if let Some(value) = value.as_bool() {
            Ok(TypedAst::Bool(value))
        } else if let Some(value) = value.as_int() {
            Ok(TypedAst::Int(value))
        } else {
            Err(anyhow!(
                "`TypedAst` supports `Int` and `Bool`, but `{:?}` was given.",
                value.sort_kind()
            ))
        }
    }
}

impl From<Int> for TypedAst {
    fn from(value: Int) -> Self {
        TypedAst::Int(value)
    }
}

impl From<Bool> for TypedAst {
    fn from(value: Bool) -> Self {
        TypedAst::Bool(value)
    }
}

impl Display for TypedAst {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TypedAst::Int(x) => write!(f, "{}", x),
            TypedAst::Bool(x) => write!(f, "{}", x),
        }
    }
}

impl TypedAst {
    /// Convert the given [`Dynamic`] value into [`TypedAst`] of the expected [`AstType`].
    ///
    /// # Panics
    ///
    /// The method panics if the given `value` has an unexpected type.
    pub fn cast_dynamic(value_type: AstType, value: Dynamic) -> TypedAst {
        match value_type {
            AstType::Int => value.as_int().map(TypedAst::Int).unwrap_or_else(|| {
                panic!("Expected `Int`, but got `{:?}`.", value.sort_kind());
            }),
            AstType::Bool => value.as_bool().map(TypedAst::Bool).unwrap_or_else(|| {
                panic!("Expected `Bool`, but got `{:?}`.", value.sort_kind());
            }),
        }
    }

    pub fn as_dyn_ref(&self) -> &dyn Ast {
        match self {
            TypedAst::Int(x) => x as &dyn Ast,
            TypedAst::Bool(x) => x as &dyn Ast,
        }
    }

    pub fn as_bool(&self) -> Option<&Bool> {
        match self {
            TypedAst::Int(_) => None,
            TypedAst::Bool(value) => Some(value),
        }
    }

    pub fn ast_type(&self) -> AstType {
        match self {
            TypedAst::Int(_) => AstType::Int,
            TypedAst::Bool(_) => AstType::Bool,
        }
    }

    pub fn sort_kind(&self) -> SortKind {
        self.ast_type().into()
    }

    /// Produce a [`Bool`] expression that is equivalent to `self <= other`.
    ///
    /// Currently, this operation is only supported if both ASTs are of the same type.
    pub fn le(&self, other: &TypedAst) -> Result<Bool, anyhow::Error> {
        match (self, other) {
            (TypedAst::Int(a), TypedAst::Int(b)) => Ok(a.le(b)),
            (TypedAst::Bool(a), TypedAst::Bool(b)) => Ok(a.implies(b)),
            _ => Err(anyhow!(
                "`{}` and `{}` are incomparable: `{:?} != {:?}`",
                self,
                other,
                self.sort_kind(),
                other.sort_kind()
            )),
        }
    }

    /// Produce a [`Bool`] expression that is equivalent to `self < other`.
    ///
    /// Currently, this operation is only supported if both ASTs are of the same type.
    pub fn lt(&self, other: &TypedAst) -> Result<Bool, anyhow::Error> {
        match (self, other) {
            (TypedAst::Int(a), TypedAst::Int(b)) => Ok(a.lt(b)),
            (TypedAst::Bool(a), TypedAst::Bool(b)) => Ok(Bool::and(&[a.not(), b.clone()])),
            _ => Err(anyhow!(
                "`{}` and `{}` are incomparable: `{:?} != {:?}`",
                self,
                other,
                self.sort_kind(),
                other.sort_kind()
            )),
        }
    }

    /// Produce a [`Bool`] expression that is equivalent to `self == other`.
    ///
    /// Currently, this operation is only supported if both ASTs are of the same type.
    pub fn eq(&self, other: &TypedAst) -> Result<Bool, anyhow::Error> {
        match (self, other) {
            (TypedAst::Int(a), TypedAst::Int(b)) => Ok(a.eq(b)),
            (TypedAst::Bool(a), TypedAst::Bool(b)) => Ok(a.iff(b)),
            _ => Err(anyhow!(
                "`{}` and `{}` are incomparable: `{:?} != {:?}`",
                self,
                other,
                self.sort_kind(),
                other.sort_kind()
            )),
        }
    }

    /// Transform fully specified [`FnUpdate`] into a Boolean [`TypedAst`] expression
    /// with all variables substituted into [`Bool`] AST nodes according
    /// to the `substitution_map`.
    ///
    /// # Panics
    ///
    /// The method panics if the given function contains parameters or if some variables
    /// are missing from the `substitution_map`.
    pub fn from_fn_update(
        fn_update: &FnUpdate,
        substitution_map: &HashMap<VariableId, Bool>,
    ) -> TypedAst {
        fn build(fn_update: &FnUpdate, map: &HashMap<VariableId, Bool>) -> Bool {
            match fn_update {
                FnUpdate::Const(value) => Bool::from_bool(*value),
                FnUpdate::Var(id) => map
                    .get(id)
                    .unwrap_or_else(|| panic!("Variable `{id}` not present in `substitution_map`."))
                    .clone(),
                FnUpdate::Param(_, _) => {
                    panic!("`TypedAst::from_fn_update` does not support parameters.")
                }
                FnUpdate::Not(inner) => build(inner, map).not(),
                FnUpdate::Binary(op, left, right) => {
                    let left = build(left, map);
                    let right = build(right, map);
                    match op {
                        BinaryOp::And => Bool::and(&[left, right]),
                        BinaryOp::Or => Bool::or(&[left, right]),
                        BinaryOp::Xor => left.xor(right),
                        BinaryOp::Iff => left.iff(right),
                        BinaryOp::Imp => left.implies(right),
                    }
                }
            }
        }

        Self::from(build(fn_update, substitution_map))
    }
}

/// A utility trait that allows us to convert iterators of different [`Ast`] instances
/// into `&dyn Ast` iterators and/or vectors.
pub trait MapDynAst<'a, T>: Sized {
    fn map_dyn(self) -> impl Iterator<Item = &'a dyn Ast>;

    fn dyn_vec(self) -> Vec<&'a dyn Ast> {
        self.map_dyn().collect::<Vec<_>>()
    }
}

impl<'a, I: Iterator<Item = &'a TypedAst>> MapDynAst<'a, &'a TypedAst> for I {
    fn map_dyn(self) -> impl Iterator<Item = &'a dyn Ast> {
        self.map(|x| x.as_dyn_ref())
    }
}

impl<'a, 'b, I: Iterator<Item = &'b &'a TypedAst>> MapDynAst<'a, &'b &'a TypedAst> for I {
    fn map_dyn(self) -> impl Iterator<Item = &'a dyn Ast> {
        self.map(|x| x.as_dyn_ref())
    }
}

impl<'a, I: Iterator<Item = &'a Bool>> MapDynAst<'a, &'a Bool> for I {
    fn map_dyn(self) -> impl Iterator<Item = &'a dyn Ast> {
        self.map(|x| x as &dyn Ast)
    }
}

impl<'a, I: Iterator<Item = &'a Int>> MapDynAst<'a, &'a Int> for I {
    fn map_dyn(self) -> impl Iterator<Item = &'a dyn Ast> {
        self.map(|x| x as &dyn Ast)
    }
}
