use crate::compiler::source::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    Identifier(String),

    Integer(i64),
    String(String),

    Extends,
    Struct,
    Fn,
    Let,
    Const,
    Return,

    True,
    False,

    Int,
    StringType,
    Bool,
    Void,

    LeftBrace,
    RightBrace,

    LeftParen,
    RightParen,

    Colon,
    Semicolon,
    Comma,
    Dot,

    Plus,
    Minus,
    Star,
    Slash,

    Equal,
    EqualEqual,

    If,
    Else,
    While,
    Break,
    Continue,

    Public,
    Private,
    Protected,

    Eof,
}