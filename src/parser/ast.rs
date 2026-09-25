use crate::{compiler::source::Span, semantic::modifiers::Visibility};

#[derive(Debug, Clone)]
pub struct Program {
    pub structs: Vec<StructDecl>,
    pub functions: Vec<FunctionDecl>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructDecl {
    pub name: String,
    pub base: Option<String>,
    pub fields: Vec<FieldDecl>,
    pub methods: Vec<FunctionDecl>,
    pub constructors: Vec<ConstructorDecl>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FieldDecl {
    pub name: String,
    pub ty: TypeName,
    pub visibility: Visibility,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ConstructorDecl {
    pub params: Vec<Param>,
    pub base_arguments: Vec<Expr>,
    pub body: Stmt,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: TypeName,
    pub body: Stmt,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: String,
    pub ty: TypeName,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Assign {
        target: Expr,
        value: Expr,
        span: Span,
    },

    Block {
        statements: Vec<Stmt>,
        span: Span,
    },

    Let {
        name: String,
        ty: TypeName,
        value: Expr,
        span: Span,
    },

    Const {
        name: String,
        ty: TypeName,
        value: Expr,
        span: Span,
    },

    Return {
        value: Option<Expr>,
        span: Span,
    },

    Expr {
        expr: Expr,
        span: Span,
    },

    If {
        condition: Expr,
        then_block: Box<Stmt>,
        else_block: Option<Box<Stmt>>,
        span: Span,
    },

    While {
        condition: Expr,
        body: Box<Stmt>,
        span: Span,
    },

    Break {
        span: Span,
    },

    Continue {
        span: Span,
    },

    New {
        name: String,
        arguments: Vec<Expr>,
        span: Span,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Integer {
        value: i64,
        span: Span,
    },

    String {
        value: String,
        span: Span,
    },

    Bool {
        value: bool,
        span: Span,
    },

    Identifier {
        name: String,
        span: Span,
    },

    Member {
        receiver: Box<Expr>,
        name: String,
        span: Span,
    },

    Binary {
        op: BinaryOp,
        left: Box<Expr>,
        right: Box<Expr>,
        span: Span,
    },

    Call {
        receiver: Option<Box<Expr>>,
        name: String,
        arguments: Vec<Expr>,
        span: Span,
    },

    New {
        name: String,
        arguments: Vec<Expr>,
        span: Span,
    },
}

impl Expr {
    pub fn span(&self) -> Span {
        match self {
            Expr::Integer { span, .. }
            | Expr::String { span, .. }
            | Expr::Bool { span, .. }
            | Expr::Identifier { span, .. }
            | Expr::Member { span, .. }
            | Expr::Binary { span, .. }
            | Expr::New { span, .. }
            | Expr::Call { span, .. } => *span,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Equal,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeName {
    Int,
    String,
    Bool,
    Void,
    Named(String),
}
