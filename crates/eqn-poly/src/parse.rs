use std::str::FromStr;

use eqn_algebra::ring::{CommutativeRing, RingElem, RingExpr};
use eqn_parser::{Ast, FromAst, FromLiteral, Grammar, ParseError};

use crate::Polynomial;

/// The [`RingExpr`] syntax, read as the polynomial the expression
/// evaluates to.
impl<R> FromAst for Polynomial<R>
where
    R: CommutativeRing,
    RingElem<R>: FromLiteral,
{
    fn grammar() -> Grammar {
        RingExpr::<R>::grammar()
    }

    fn from_ast(ast: Ast) -> Result<Self, ParseError> {
        RingExpr::<R>::from_ast(ast).map(Self::from)
    }
}

impl<R> FromStr for Polynomial<R>
where
    R: CommutativeRing,
    RingElem<R>: FromLiteral,
{
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}
