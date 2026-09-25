use std::sync::Arc;

use miette::SourceSpan;

#[derive(Debug, Clone)]
pub struct SourceFile {
    pub text: Arc<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    pub fn len(&self) -> usize {
        self.end.saturating_sub(self.start)
    }

    pub fn to_source_span(self) -> SourceSpan {
        (self.start, self.len()).into()
    }
}

impl SourceFile {
    pub fn new(src_file: &str) -> Self {
        Self {
            text: Arc::new(src_file.to_owned()),
        }
    }

    pub fn slice(&self, start: usize, end: usize) -> &str {
        &self.text[start..end]
    }
}
