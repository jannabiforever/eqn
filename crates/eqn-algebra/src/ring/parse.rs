use std::num::NonZeroUsize;
use std::str::FromStr;

use eqn_core::symbol::Symbol;
use eqn_parser::{Assoc, Ast, FromAst, FromLiteral, Grammar, ParseError};

use super::{Ring, RingElem, RingExpr, SemiRing, SemiRingExpr};

/// `x^n` with a positive integer literal `n`.
fn exponent(ast: &Ast) -> Result<NonZeroUsize, ParseError> {
    ast.integer("-")
        .and_then(|n| usize::try_from(n).ok())
        .and_then(NonZeroUsize::new)
        .ok_or_else(|| {
            ParseError::new(format!(
                "exponent must be a positive integer literal, found `{ast}`"
            ))
        })
}

fn sum(op: &str) -> Option<bool> {
    match op {
        "+" => Some(false),
        "-" => Some(true),
        _ => None,
    }
}

fn product(op: &str) -> Option<bool> {
    (op == "*").then_some(false)
}

/// `+`, `*` (or juxtaposition) and `x^n` for `n >= 1`. Prefix `-` exists
/// only to spell negative constants: a semi-ring has no inverses, so `-x`
/// is an error and `a - b` is not even syntax.
impl<SR> FromAst for SemiRingExpr<SR>
where
    SR: SemiRing,
    RingElem<SR>: FromLiteral,
{
    fn grammar() -> Grammar {
        Grammar::new()
            .infix("+", 1, Assoc::Left)
            .infix("*", 2, Assoc::Left)
            .juxtaposition("*")
            .prefix("-", 3)
            .infix("^", 4, Assoc::Right)
    }

    fn from_ast(ast: Ast) -> Result<Self, ParseError> {
        if let Some(text) = ast.literal("-") {
            return RingElem::<SR>::from_literal(&text).map(Self::Const);
        }
        match ast {
            Ast::Ident(name) => Ok(Self::Symbol(Symbol::new(name))),
            Ast::Group(inner) => Self::from_ast(*inner),
            Ast::Infix(ref op, ..) if op == "+" => ast
                .operands(sum)
                .into_iter()
                .map(|(_, term)| Self::from_ast(term))
                .collect::<Result<_, _>>()
                .map(Self::Add),
            Ast::Infix(ref op, ..) if op == "*" => ast
                .operands(product)
                .into_iter()
                .map(|(_, factor)| Self::from_ast(factor))
                .collect::<Result<_, _>>()
                .map(Self::Mul),
            Ast::Infix(op, base, exp) if op == "^" => Ok(Self::Pow {
                exponent: exponent(&exp)?,
                base: Box::new(Self::from_ast(*base)?),
            }),
            Ast::Infix(op, ..) | Ast::Prefix(op, _) | Ast::Postfix(op, _) => Err(ParseError::new(
                format!("semi-ring expressions have no `{op}` operator"),
            )),
            Ast::Call(name, _) => Err(ParseError::new(format!("unknown function `{name}`"))),
            Ast::Number(_) => unreachable!("literals are handled above"),
        }
    }
}

impl<SR> FromStr for SemiRingExpr<SR>
where
    SR: SemiRing,
    RingElem<SR>: FromLiteral,
{
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        eqn_parser::parse(s)
    }
}

/// The [`SemiRingExpr`] syntax plus negation: prefix `-`, and `a - b` as
/// `a + (-b)`.
impl<R> FromAst for RingExpr<R>
where
    R: Ring,
    RingElem<R>: FromLiteral,
{
    fn grammar() -> Grammar {
        SemiRingExpr::<R>::grammar().infix("-", 1, Assoc::Left)
    }

    fn from_ast(ast: Ast) -> Result<Self, ParseError> {
        if let Some(text) = ast.literal("-") {
            return RingElem::<R>::from_literal(&text).map(Self::Const);
        }
        match ast {
            Ast::Ident(name) => Ok(Self::Symbol(Symbol::new(name))),
            Ast::Group(inner) => Self::from_ast(*inner),
            Ast::Prefix(_, inner) => Self::from_ast(*inner).map(negate),
            Ast::Infix(ref op, ..) if op == "+" || op == "-" => ast
                .operands(sum)
                .into_iter()
                .map(|(negated, term)| {
                    let term = Self::from_ast(term)?;
                    Ok(if negated { negate(term) } else { term })
                })
                .collect::<Result<_, _>>()
                .map(Self::Add),
            Ast::Infix(ref op, ..) if op == "*" => ast
                .operands(product)
                .into_iter()
                .map(|(_, factor)| Self::from_ast(factor))
                .collect::<Result<_, _>>()
                .map(Self::Mul),
            Ast::Infix(op, base, exp) if op == "^" => Ok(Self::Pow {
                exponent: exponent(&exp)?,
                base: Box::new(Self::from_ast(*base)?),
            }),
            Ast::Infix(op, ..) | Ast::Postfix(op, _) => Err(ParseError::new(format!(
                "ring expressions have no `{op}` operator"
            ))),
            Ast::Call(name, _) => Err(ParseError::new(format!("unknown function `{name}`"))),
            Ast::Number(_) => unreachable!("literals are handled above"),
        }
    }
}

fn negate<R: Ring>(expr: RingExpr<R>) -> RingExpr<R> {
    RingExpr::Neg(Box::new(expr))
}

impl<R> FromStr for RingExpr<R>
where
    R: Ring,
    RingElem<R>: FromLiteral,
{
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        eqn_parser::parse(s)
    }
}

#[cfg(test)]
mod tests {
    use eqn_core::set::Z;

    use super::*;
    use crate::operator_impl::{ZAdd, ZMul};

    type Integers = (Z, ZAdd, ZMul);
    type Expr = SemiRingExpr<Integers>;
    type RExpr = RingExpr<Integers>;

    fn pow<E>(base: E, exponent: usize) -> (Box<E>, NonZeroUsize) {
        (Box::new(base), NonZeroUsize::new(exponent).unwrap())
    }

    #[test]
    fn semi_ring_syntax() {
        let x = Expr::Symbol(Symbol::new("x"));
        let (base, exponent) = pow(x.clone(), 2);
        assert_eq!(
            "1 + 2 x + x^2 * (x + 1)".parse::<Expr>().unwrap(),
            Expr::Add(vec![
                Expr::Const(1),
                Expr::Mul(vec![Expr::Const(2), x.clone()]),
                Expr::Mul(vec![
                    Expr::Pow { base, exponent },
                    Expr::Add(vec![x, Expr::Const(1)]),
                ]),
            ])
        );
    }

    #[test]
    fn semi_rings_have_no_inverses() {
        assert_eq!(
            "x - 1".parse::<Expr>().unwrap_err(),
            ParseError::at(2, "unexpected `-`")
        );
        assert_eq!(
            "-x".parse::<Expr>().unwrap_err(),
            ParseError::new("semi-ring expressions have no `-` operator")
        );
        assert_eq!(
            "x / 2".parse::<Expr>().unwrap_err(),
            ParseError::at(2, "unexpected `/`")
        );
        assert_eq!(
            "x^0".parse::<Expr>().unwrap_err(),
            ParseError::new("exponent must be a positive integer literal, found `0`")
        );
        assert_eq!(
            "x^-1".parse::<Expr>().unwrap_err(),
            ParseError::new("exponent must be a positive integer literal, found `-1`")
        );
        assert!("-1".parse::<Expr>().is_ok(), "a negative constant is fine");
    }

    #[test]
    fn ring_syntax_adds_negation() {
        let x = || RExpr::Symbol(Symbol::new("x"));
        assert_eq!(
            "2 x - 5 x + -(x)".parse::<RExpr>().unwrap(),
            RExpr::Add(vec![
                RExpr::Mul(vec![RExpr::Const(2), x()]),
                negate(RExpr::Mul(vec![RExpr::Const(5), x()])),
                negate(x()),
            ])
        );
        assert_eq!("-3".parse::<RExpr>().unwrap(), RExpr::Const(-3));
        assert_eq!("--x".parse::<RExpr>().unwrap(), negate(negate(x())));
        assert_eq!(
            "x / 2".parse::<RExpr>().unwrap_err(),
            ParseError::at(2, "unexpected `/`")
        );
    }
}
