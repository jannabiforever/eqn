//! Text syntax for expression trees.
//!
//! Parsing is split in two so that the grammar is written once and each
//! expression type only decides what it can represent:
//!
//! 1. [`parse_ast`] reads source text into an untyped [`Ast`] using the
//!    precedence table below.
//! 2. [`FromAst`] lowers the [`Ast`] into a concrete expression tree. Each
//!    expression type implements it and rejects the syntax it has no node for
//!    (a semi-ring has no `-`, a monoid has no `^`, ...).
//!
//! [`parse`] runs both stages. Expression types expose it through
//! [`FromStr`], so `"x + 2 * y".parse::<RingExpr<R>>()` is the intended entry
//! point.
//!
//! # Syntax
//!
//! | precedence (low to high) | syntax                                  | associativity |
//! |--------------------------|-----------------------------------------|---------------|
//! | 1                        | `a + b`, `a - b`                        | left          |
//! | 2                        | `a ∧ b` (also spelled `a /\ b`)         | left          |
//! | 3                        | `a * b`, `a / b`, juxtaposition `a b`   | left          |
//! | 4                        | `-a`                                    | prefix        |
//! | 5                        | `a ^ b`                                 | right         |
//!
//! Atoms are numeric literals (`3`, `2.5`), identifiers (`x`, `θ`, `x_1`,
//! `x'`), calls `f(a, b)` and parenthesized expressions. Which functions
//! exist, and what a literal means, is up to the lowering: the [`Ast`] keeps
//! the literal's text and each expression type reads it through
//! [`FromLiteral`].
//!
//! Parentheses survive as [`Ast::Group`] nodes, so `a + b + c` and
//! `a + (b + c)` lower to different trees: lowering flattens the former into
//! one n-ary sum but never looks through parentheses. The text form is thus
//! a faithful notation for one specific tree, which is what tests need.
//!
//! A negated literal such as `-3` lowers to the constant `-3`, not to the
//! negation of `3`. `-x^2` is `-(x^2)`, and `x^-2` has exponent `-2`.

use std::fmt::Display;
use std::str::FromStr;

mod ast;
mod error;
mod lexer;
mod parser;

pub use ast::{Ast, BinaryOp, UnaryOp};
pub use error::ParseError;
pub use lexer::{Token, tokenize};
pub use parser::parse_ast;

/// Lowers an untyped [`Ast`] into a typed expression tree.
///
/// Implementations should be structural: every syntax node maps to one tree
/// node, and syntax the type cannot represent is an error rather than being
/// rewritten into something else.
pub trait FromAst: Sized {
    fn from_ast(ast: Ast) -> Result<Self, ParseError>;
}

/// Parses `src` and lowers it into `T`.
pub fn parse<T: FromAst>(src: &str) -> Result<T, ParseError> {
    T::from_ast(parse_ast(src)?)
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
