use crate::parser::ast::TypeName;

use super::symbols::StructId;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int,
    String,
    Bool,
    Void,

    Struct(StructId),
}

impl Type {
    pub fn from_ast_builtin(ty: &TypeName) -> Option<Self> {
        match ty {
            TypeName::Int => Some(Self::Int),

            TypeName::String => Some(Self::String),

            TypeName::Bool => Some(Self::Bool),

            TypeName::Void => Some(Self::Void),

            TypeName::Named(_) => None,
        }
    }
}
