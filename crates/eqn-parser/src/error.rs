use std::fmt;

/// A lexing, parsing or lowering failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseError {
    message: String,
    /// Byte offset into the source, when known. Lowering errors have none:
    /// the [`Ast`](crate::Ast) carries no spans.
    offset: Option<usize>,
}

impl ParseError {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            offset: None,
        }
    }

    pub fn at(offset: usize, message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            offset: Some(offset),
        }
    }

    pub fn message(&self) -> &str {
        &self.message
    }

    pub fn offset(&self) -> Option<usize> {
        self.offset
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.offset {
            Some(offset) => write!(f, "{} (at byte {offset})", self.message),
            None => f.write_str(&self.message),
        }
    }
}

impl std::error::Error for ParseError {}
