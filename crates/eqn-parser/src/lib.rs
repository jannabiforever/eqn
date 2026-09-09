//! Text syntax for expression trees.
//!
//! Parsing is split in two so that the machinery is written once while each
//! expression type keeps full control of its own syntax:
//!
//! 1. [`parse_ast`] reads source text into an untyped [`Ast`], driven by a
//!    [`Grammar`]: the table of operator symbols with their fixity, precedence
//!    and associativity. This crate declares no operators of its own; `+` is an
//!    operator only where a grammar says so, and `⊕` or `\oplus` are declared
//!    the same way.
//! 2. [`FromAst`] pairs a grammar with a lowering from [`Ast`] into a concrete
//!    expression tree. Operators reach the lowering by their spelling, and the
//!    lowering decides what each one means and rejects what it has no node for.
//!
//! [`parse`] runs both stages. Expression types expose it through
//! [`FromStr`], so `"x + 2 * y".parse::<RingExpr<R>>()` is the intended entry
//! point.
//!
//! # Syntax
//!
//! Always available: numeric literals (`3`, `2.5`), identifiers (`x`, `θ`,
//! `x_1`; a letter or `_` followed by letters, digits or `_`), calls
//! `f(a, b)` and parentheses. An identifier directly followed by `(` is
//! always a call. What a literal means is up to the lowering: the [`Ast`]
//! keeps its text and each expression type reads it through [`FromLiteral`].
//!
//! Declared by the grammar: prefix, infix and postfix operators, and
//! optionally which infix operator juxtaposition (`2 x`, `2(x + 1)`) stands
//! for. Operator symbols may be any text that does not start like an
//! identifier or a number, so `∧`, `**` and `\oplus` all work; the lexer
//! matches the longest declared symbol.
//!
//! Parentheses survive as [`Ast::Group`] nodes, so `a + b + c` and
//! `a + (b + c)` lower to different trees: lowering flattens the former into
//! one n-ary sum but never looks through parentheses. The text form is thus
//! a faithful notation for one specific tree, which is what tests need.

use std::fmt::Display;
use std::str::FromStr;

mod ast;
mod error;
mod grammar;
mod lexer;
mod parser;

pub use ast::Ast;
pub use error::ParseError;
pub use grammar::{Assoc, Grammar};
pub use lexer::{Token, tokenize};
pub use parser::parse_ast;

/// A grammar together with a lowering of its [`Ast`] into a typed tree.
///
/// Lowerings should be structural: every syntax node maps to one tree node,
/// and syntax the type cannot represent is an error rather than being
/// rewritten into something else.
pub trait FromAst: Sized {
    /// The operators this type's syntax has.
    fn grammar() -> Grammar;

    fn from_ast(ast: Ast) -> Result<Self, ParseError>;
}

/// Parses `src` with `T`'s grammar and lowers it into `T`.
pub fn parse<T: FromAst>(src: &str) -> Result<T, ParseError> {
    T::from_ast(parse_ast(src, &T::grammar())?)
}

/// A domain element readable from a numeric literal such as `3`, `-3` or
/// `2.5`.
///
/// Every [`FromStr`] type whose error can be displayed is a literal for
/// free; anything else may implement this directly.
pub trait FromLiteral: Sized {
    fn from_literal(text: &str) -> Result<Self, ParseError>;
}

impl<T> FromLiteral for T
where
    T: FromStr,
    T::Err: Display,
{
    fn from_literal(text: &str) -> Result<Self, ParseError> {
        text.parse()
            .map_err(|e| ParseError::new(format!("invalid constant `{text}`: {e}")))
    }
}
