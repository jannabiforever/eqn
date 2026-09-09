use std::str::FromStr;

use eqn_core::symbol::Symbol;
use eqn_parser::{Ast, BinaryOp, FromAst, FromLiteral, ParseError};

use super::{Monoid, MonoidElem, MonoidExpr};

/// `+`, `*` and juxtaposition all denote the monoid operation, so an
/// additive monoid reads as `x + y` and a multiplicative one as `x * y`.
/// Chains flatten into one [`MonoidExpr::Op`]; parentheses nest.
impl<M> FromAst for MonoidExpr<M>
where
    M: Monoid,
    MonoidElem<M>: FromLiteral,
{
    fn from_ast(ast: Ast) -> Result<Self, ParseError> {
        if let Some(text) = ast.literal() {
            return MonoidElem::<M>::from_literal(&text).map(Self::Const);
        }
        match ast {
            Ast::Ident(name) => Ok(Self::Symbol(Symbol::new(name))),
            Ast::Group(inner) => Self::from_ast(*inner),
            Ast::Binary(op, ..) if operation(op).is_some() => ast
                .operands(operation)
                .into_iter()
                .map(|(_, operand)| Self::from_ast(operand))
                .collect::<Result<_, _>>()
                .map(Self::Op),
            Ast::Binary(op, ..) => Err(ParseError::new(format!(
                "monoid expressions have no `{op}` operator"
            ))),
            Ast::Unary(op, _) => Err(ParseError::new(format!(
                "monoid expressions have no prefix `{op}`"
            ))),
            Ast::Call(name, _) => Err(ParseError::new(format!("unknown function `{name}`"))),
            Ast::Number(_) => unreachable!("literals are handled above"),
        }
    }
}

fn operation(op: BinaryOp) -> Option<bool> {
    matches!(op, BinaryOp::Add | BinaryOp::Mul).then_some(false)
}

impl<M> FromStr for MonoidExpr<M>
where
    M: Monoid,
    MonoidElem<M>: FromLiteral,
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
    use crate::operator_impl::ZAdd;

    type Expr = MonoidExpr<(Z, ZAdd)>;

    fn x() -> Expr {
        Expr::Symbol(Symbol::new("x"))
    }

    #[test]
    fn plus_star_and_juxtaposition_are_the_operation() {
        let expected = Expr::Op(vec![Expr::Const(1), x(), Expr::Const(-2)]);
        assert_eq!("1 + x + -2".parse::<Expr>().unwrap(), expected);
        assert_eq!("1 * x * -2".parse::<Expr>().unwrap(), expected);
        assert_eq!("1 (x) (-2)".parse::<Expr>().unwrap(), expected);
    }

    #[test]
    fn parentheses_nest() {
        assert_eq!(
            "1 + (x + 2)".parse::<Expr>().unwrap(),
            Expr::Op(vec![Expr::Const(1), Expr::Op(vec![x(), Expr::Const(2)])])
        );
        assert_eq!("(x)".parse::<Expr>().unwrap(), x());
    }

    #[test]
    fn rejects_what_a_monoid_cannot_express() {
        assert_eq!(
            "x - 1".parse::<Expr>().unwrap_err(),
            ParseError::new("monoid expressions have no `-` operator")
        );
        assert_eq!(
            "x ^ 2".parse::<Expr>().unwrap_err(),
            ParseError::new("monoid expressions have no `^` operator")
        );
        assert_eq!(
            "-x".parse::<Expr>().unwrap_err(),
            ParseError::new("monoid expressions have no prefix `-`")
        );
        assert_eq!(
            "inv(x)".parse::<Expr>().unwrap_err(),
            ParseError::new("unknown function `inv`")
        );
        assert!("2.5".parse::<Expr>().is_err());
        assert!("x +".parse::<Expr>().is_err());
    }
}
