use std::num::NonZeroUsize;
use std::str::FromStr;

use eqn_core::symbol::Symbol;
use eqn_parser::{Assoc, Ast, FromAst, FromLiteral, Grammar, ParseError};

use super::{Ring, RingElem, RingExpr, SemiRing, SemiRingExpr};

/// [`SemiRing::ADD_SYMBOL`], [`SemiRing::MUL_SYMBOL`] (or juxtaposition)
/// and `x^n` for `n >= 1`. Prefix `-` exists only to spell negative
/// constants: a semi-ring has no inverses, so `-x` is an error and `a - b`
/// is not even syntax.
impl<SR> FromAst for SemiRingExpr<SR>
where
    SR: SemiRing,
    RingElem<SR>: FromLiteral,
{
    fn grammar() -> anyhow::Result<Grammar> {
        Grammar::new()
            .infix(SR::ADD_SYMBOL, 1, Assoc::Left)?
            .infix(SR::MUL_SYMBOL, 2, Assoc::Left)?
            .juxtaposition(SR::MUL_SYMBOL)?
            .prefix("-", 3)?
            .infix("^", 4, Assoc::Right)
    }

    fn from_ast(ast: Ast) -> Result<Self, ParseError> {
        if let Some(text) = ast.literal("-") {
            return RingElem::<SR>::from_literal(&text).map(Self::Const);
        }
        match ast {
            Ast::Ident(name) => Ok(Self::Symbol(Symbol::new(name))),
            Ast::Group(inner) => Self::from_ast(*inner),
            Ast::Infix(ref op, ..) if op == SR::ADD_SYMBOL => ast
                .operands(|op| (op == SR::ADD_SYMBOL).then_some(false))
                .into_iter()
                .map(|(_, term)| Self::from_ast(term))
                .collect::<Result<_, _>>()
                .map(Self::Add),
            Ast::Infix(ref op, ..) if op == SR::MUL_SYMBOL => ast
                .operands(|op| (op == SR::MUL_SYMBOL).then_some(false))
                .into_iter()
                .map(|(_, factor)| Self::from_ast(factor))
                .collect::<Result<_, _>>()
                .map(Self::Mul),
            Ast::Infix(op, base, exp) if op == "^" => Ok(Self::Pow {
                exponent: Self::exponent(&exp)?,
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

impl<SR: SemiRing> SemiRingExpr<SR> {
    /// The `n` of `x^n`: a positive integer literal.
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
}

impl<SR> FromStr for SemiRingExpr<SR>
where
    SR: SemiRing,
    RingElem<SR>: FromLiteral,
{
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

/// The [`SemiRingExpr`] syntax plus negation: prefix [`Ring::SUB_SYMBOL`],
/// and `a - b` as `a + (-b)`.
impl<R> FromAst for RingExpr<R>
where
    R: Ring,
    RingElem<R>: FromLiteral,
{
    fn grammar() -> anyhow::Result<Grammar> {
        SemiRingExpr::<R>::grammar()?
            .infix(R::SUB_SYMBOL, 1, Assoc::Left)?
            .prefix(R::SUB_SYMBOL, 3)
    }

    fn from_ast(ast: Ast) -> Result<Self, ParseError> {
        if let Some(text) = ast.literal("-") {
            return RingElem::<R>::from_literal(&text).map(Self::Const);
        }
        match ast {
            Ast::Ident(name) => Ok(Self::Symbol(Symbol::new(name))),
            Ast::Group(inner) => Self::from_ast(*inner),
            Ast::Prefix(op, inner) if op == R::SUB_SYMBOL => {
                Self::from_ast(*inner).map(Self::negated)
            }
            Ast::Infix(ref op, ..) if op == R::ADD_SYMBOL || op == R::SUB_SYMBOL => ast
                .operands(Self::sum)
                .into_iter()
                .map(|(negated, term)| {
                    let term = Self::from_ast(term)?;
                    Ok(if negated { term.negated() } else { term })
                })
                .collect::<Result<_, _>>()
                .map(Self::Add),
            Ast::Infix(ref op, ..) if op == R::MUL_SYMBOL => ast
                .operands(|op| (op == R::MUL_SYMBOL).then_some(false))
                .into_iter()
                .map(|(_, factor)| Self::from_ast(factor))
                .collect::<Result<_, _>>()
                .map(Self::Mul),
            Ast::Infix(op, base, exp) if op == "^" => Ok(Self::Pow {
                exponent: SemiRingExpr::<R>::exponent(&exp)?,
                base: Box::new(Self::from_ast(*base)?),
            }),
            Ast::Infix(op, ..) | Ast::Prefix(op, _) | Ast::Postfix(op, _) => Err(ParseError::new(
                format!("ring expressions have no `{op}` operator"),
            )),
            Ast::Call(name, _) => Err(ParseError::new(format!("unknown function `{name}`"))),
            Ast::Number(_) => unreachable!("literals are handled above"),
        }
    }
}

impl<R: Ring> RingExpr<R> {
    fn negated(self) -> Self {
        Self::Neg(Box::new(self))
    }

    /// Classifies `op` for [`Ast::operands`]: `a + b - c` is one sum, with
    /// the terms after [`Ring::SUB_SYMBOL`] negated.
    fn sum(op: &str) -> Option<bool> {
        if op == R::ADD_SYMBOL {
            Some(false)
        } else if op == R::SUB_SYMBOL {
            Some(true)
        } else {
            None
        }
    }
}

impl<R> FromStr for RingExpr<R>
where
    R: Ring,
    RingElem<R>: FromLiteral,
{
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

#[cfg(test)]
mod tests {

    use eqn_core::set::Z;

    use super::*;
    use crate::operator_impl::{ZAdd, ZMul};

    type Integers = (ZAdd, ZMul);
    type Expr = SemiRingExpr<Integers>;
    type RExpr = RingExpr<Integers>;

    fn pow<E>(base: E, exponent: usize) -> (Box<E>, NonZeroUsize) {
        (Box::new(base), NonZeroUsize::new(exponent).unwrap())
    }

    fn error<E: FromStr<Err = anyhow::Error> + std::fmt::Debug>(src: &str) -> ParseError {
        src.parse::<E>().unwrap_err().downcast().unwrap()
    }

    #[test]
    fn sums_products_and_powers_lower_structurally() {
        let x = Expr::Symbol(Symbol::new("x"));
        let (base, exponent) = pow(x.clone(), 2);
        assert_eq!(
            "1 + 2 x + x^2 * (x + 1)".parse::<Expr>().unwrap(),
            Expr::Add(vec![
                Expr::Const(Z::from(1)),
                Expr::Mul(vec![Expr::Const(Z::from(2)), x.clone()]),
                Expr::Mul(vec![
                    Expr::Pow { base, exponent },
                    Expr::Add(vec![x, Expr::Const(Z::from(1))]),
                ]),
            ])
        );
    }

    #[test]
    fn semi_rings_have_no_inverses() {
        assert_eq!(error::<Expr>("x - 1"), ParseError::at(2, "unexpected `-`"));
        assert_eq!(
            error::<Expr>("-x"),
            ParseError::new("semi-ring expressions have no `-` operator")
        );
        assert_eq!(error::<Expr>("x / 2"), ParseError::at(2, "unexpected `/`"));
        assert_eq!(
            error::<Expr>("x^0"),
            ParseError::new("exponent must be a positive integer literal, found `0`")
        );
        assert_eq!(
            error::<Expr>("x^-1"),
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
                RExpr::Mul(vec![RExpr::Const(Z::from(2)), x()]),
                RExpr::Mul(vec![RExpr::Const(Z::from(5)), x()]).negated(),
                x().negated(),
            ])
        );
        assert_eq!("-3".parse::<RExpr>().unwrap(), RExpr::Const(Z::from(-3)));
        assert_eq!("--x".parse::<RExpr>().unwrap(), x().negated().negated());
        assert_eq!(error::<RExpr>("x / 2"), ParseError::at(2, "unexpected `/`"));
    }
}
