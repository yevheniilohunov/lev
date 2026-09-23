use std::fmt;

use crate::compiler::source::Span;
use crate::semantic::symbols::ConstructorId;

use super::symbols::{ FunctionId, LocalId, StructId };

use super::types::Type;

#[derive(Debug)]
pub struct HirProgram {
    pub structs: Vec<HirStruct>,
    pub functions: Vec<HirFunction>,
}

#[derive(Debug)]
pub struct HirStruct {
    pub id: StructId,
    pub name: String,
    pub base: Option<StructId>,
    pub fields: Vec<HirField>,
}

#[derive(Debug)]
pub struct HirField {
    pub name: String,
    pub ty: Type,
}

#[derive(Debug)] pub struct HirFunction { 
    pub id: Option<FunctionId>,
    pub constructor_id: Option<ConstructorId>,
    pub name: String, 
    // None for top-level functions. 
    // Some(struct_id) for struct methods. 
    pub owner: Option<StructId>, 
    pub params: Vec<HirParam>, 
    pub locals: Vec<HirLocal>, 
    pub return_type: Type, 
    pub body: HirBlock,
 }

#[derive(Debug)]
pub struct HirParam {
    pub local: LocalId,
    pub name: String,
    pub ty: Type,
}

#[derive(Debug)]
pub struct HirLocal {
    pub id: LocalId,
    pub name: String,
    pub ty: Type,
}

#[derive(Debug)]
pub struct HirBlock {
    pub statements: Vec<HirStmt>,
}

#[derive(Debug)]
pub enum HirStmt {
    Assign {
        local: LocalId,
        value: HirExpr,
    },

    Let {
        local: LocalId,
        value: HirExpr,
    },

    Const {
        local: LocalId,
        value: HirExpr,
    },

    Return {
        value: Option<HirExpr>,
    },

    Expr(HirExpr),

    If {
        condition: HirExpr,
        then_block: HirBlock,
        else_block: Option<HirBlock>,
    },

    While {
        condition: HirExpr,
        body: HirBlock,
    },

    Break,

    Continue,
}

#[derive(Debug)]
pub struct HirExpr {
    pub kind: HirExprKind,
    pub ty: Type,
    pub span: Span,
}

impl fmt::Display for HirExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ty {:?} start to end {}..{} and HirExprKind {:?}", self.ty, self.span.start, self.span.end, self.kind)
    }
}

#[derive(Debug)]
pub enum HirExprKind {
    Integer(i64),

    String(String),

    Bool(bool),

    Local(LocalId),

    Binary {
        left: Box<HirExpr>,
        op: HirBinaryOp,
        right: Box<HirExpr>,
    },

    Call {
        function: FunctionId,
        arguments: Vec<HirExpr>,
    },

    ConstructorCall {
        constructor: ConstructorId,
        arguments: Vec<HirExpr>,
    },

    StructInit {
        struct_id: StructId,
        constructor: Option<ConstructorId>,
        arguments: Vec<HirExpr>,
    },

    Field {
        receiver: Box<HirExpr>,
        struct_id: StructId,
        field: usize,
    },
}

#[derive(Debug, Clone, Copy)]
pub enum HirBinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Equal,
}
