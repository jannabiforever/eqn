use std::str::FromStr;

use eqn_core::symbol::Symbol;
use eqn_parser::{Assoc, Ast, FromAst, FromLiteral, Grammar, ParseError};

use super::{Monoid, MonoidElem, MonoidExpr};

/// [`Monoid::SYMBOL`] and juxtaposition denote the monoid operation, so an
/// additive monoid reads as `x + y` and a multiplicative one as `x * y`.
/// Chains flatten into one [`MonoidExpr::Op`]; parentheses nest. Prefix `-`
/// exists only to spell negative constants.
impl<M> FromAst for MonoidExpr<M>
where
    M: Monoid,
    MonoidElem<M>: FromLiteral,
{
    fn grammar() -> anyhow::Result<Grammar> {
        Grammar::new()
            .infix(M::SYMBOL, 1, Assoc::Left)?
            .juxtaposition(M::SYMBOL)?
            .prefix("-", 3)
    }

    fn from_ast(ast: Ast) -> Result<Self, ParseError> {
        if let Some(text) = ast.literal("-") {
            return MonoidElem::<M>::from_literal(&text).map(Self::Const);
        }
        match ast {
            Ast::Ident(name) => Ok(Self::Symbol(Symbol::new(name))),
            Ast::Group(inner) => Self::from_ast(*inner),
            Ast::Infix(..) => ast
                .operands(|op| (op == M::SYMBOL).then_some(false))
                .into_iter()
                .map(|(_, operand)| Self::from_ast(operand))
                .collect::<Result<_, _>>()
                .map(Self::Op),
            Ast::Prefix(op, _) | Ast::Postfix(op, _) => Err(ParseError::new(format!(
                "monoid expressions have no `{op}` operator"
            ))),
            Ast::Call(name, _) => Err(ParseError::new(format!("unknown function `{name}`"))),
            Ast::Number(_) => unreachable!("literals are handled above"),
        }
    }
}

impl<M> FromStr for MonoidExpr<M>
where
    M: Monoid,
    MonoidElem<M>: FromLiteral,
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
    use crate::operator_impl::ZAdd;

    type Expr = MonoidExpr<(ZAdd,)>;

    fn x() -> Expr {
        Expr::Symbol(Symbol::new("x"))
    }

    fn error(src: &str) -> ParseError {
        src.parse::<Expr>().unwrap_err().downcast().unwrap()
    }

    #[test]
    fn symbol_and_juxtaposition_are_the_operation() {
        let expected = Expr::Op(vec![Expr::Const(Z::from(1)), x(), Expr::Const(Z::from(-2))]);
        assert_eq!("1 + x + -2".parse::<Expr>().unwrap(), expected);
        assert_eq!("1 (x) (-2)".parse::<Expr>().unwrap(), expected);
        assert_eq!(error("1 * x"), ParseError::at(2, "unexpected `*`"));
    }

    #[test]
    fn parentheses_nest() {
        assert_eq!(
            "1 + (x + 2)".parse::<Expr>().unwrap(),
            Expr::Op(vec![
                Expr::Const(Z::from(1)),
                Expr::Op(vec![x(), Expr::Const(Z::from(2))])
            ])
        );
        assert_eq!("(x)".parse::<Expr>().unwrap(), x());
    }

    #[test]
    fn rejects_what_a_monoid_cannot_express() {
        assert_eq!(error("x - 1"), ParseError::at(2, "unexpected `-`"));
        assert_eq!(error("x ^ 2"), ParseError::at(2, "unexpected `^`"));
        assert_eq!(
            error("-x"),
            ParseError::new("monoid expressions have no `-` operator")
        );
        assert_eq!(error("inv(x)"), ParseError::new("unknown function `inv`"));
        assert!("2.5".parse::<Expr>().is_err());
        assert!("x +".parse::<Expr>().is_err());
    }
}
