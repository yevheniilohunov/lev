use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

#[derive(Debug, Clone, Error, Diagnostic)]
#[error("{message}")]
pub struct CompilerError {
    pub message: String,

    #[source_code]
    pub src: Option<String>,

    #[label]
    pub span: Option<SourceSpan>,
}

impl CompilerError {
    pub fn new(source: &str, message: impl Into<String>, span: SourceSpan) -> Self {
        Self {
            message: message.into(),
            src: Some(source.to_owned()),
            span: Some(span),
        }
    }

    pub fn internal(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            src: None,
            span: None,
        }
    }
}
