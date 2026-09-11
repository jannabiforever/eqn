use std::str::FromStr;

use eqn_core::symbol::Symbol;
use eqn_parser::{Assoc, Ast, FromAst, FromLiteral, Grammar, ParseError};

use super::{Group, GroupExpr};
use crate::monoid::MonoidElem;

/// [`Monoid::SYMBOL`](crate::monoid::Monoid::SYMBOL) and juxtaposition
/// denote the group operation; infix [`Group::INVERSE_SYMBOL`] inverts its
/// right operand, prefix `INVERSE_SYMBOL` and `inv(x)` invert, and `x^n`
/// takes any integer literal exponent. `x^-1` stays a [`GroupExpr::Pow`],
/// distinct from `inv(x)`. Prefix `-` always spells negative constants.
impl<G> FromAst for GroupExpr<G>
where
    G: Group,
    MonoidElem<G>: FromLiteral,
{
    fn grammar() -> Grammar {
        Grammar::new()
            .infix(G::SYMBOL, 1, Assoc::Left)
            .infix(G::INVERSE_SYMBOL, 1, Assoc::Left)
            .juxtaposition(G::SYMBOL)
            .prefix("-", 3)
            .prefix(G::INVERSE_SYMBOL, 3)
            .infix("^", 4, Assoc::Right)
    }

    fn from_ast(ast: Ast) -> Result<Self, ParseError> {
        if let Some(text) = ast.literal("-") {
            return MonoidElem::<G>::from_literal(&text).map(Self::Const);
        }
        match ast {
            Ast::Ident(name) => Ok(Self::Symbol(Symbol::new(name))),
            Ast::Group(inner) => Self::from_ast(*inner),
            Ast::Prefix(op, inner) if op == G::INVERSE_SYMBOL => {
                Self::from_ast(*inner).map(inverse)
            }
            Ast::Infix(op, base, exponent) if op == "^" => {
                let exponent = exponent.integer("-").ok_or_else(|| {
                    ParseError::new(format!(
                        "exponent must be an integer literal, found `{exponent}`"
                    ))
                })?;
                Ok(Self::Pow {
                    base: Box::new(Self::from_ast(*base)?),
                    exponent,
                })
            }
            Ast::Infix(..) => ast
                .operands(operation::<G>)
                .into_iter()
                .map(|(inverted, operand)| {
                    let operand = Self::from_ast(operand)?;
                    Ok(if inverted { inverse(operand) } else { operand })
                })
                .collect::<Result<_, _>>()
                .map(Self::Op),
            Ast::Prefix(op, _) | Ast::Postfix(op, _) => Err(ParseError::new(format!(
                "group expressions have no `{op}` operator"
            ))),
            Ast::Call(name, mut args) if name == "inv" && args.len() == 1 => {
                Self::from_ast(args.pop().unwrap()).map(inverse)
            }
            Ast::Call(name, _) => Err(ParseError::new(format!("unknown function `{name}`"))),
            Ast::Number(_) => unreachable!("literals are handled above"),
        }
    }
}

fn inverse<G: Group>(expr: GroupExpr<G>) -> GroupExpr<G> {
    GroupExpr::Inv(Box::new(expr))
}

fn operation<G: Group>(op: &str) -> Option<bool> {
    if op == G::SYMBOL {
        Some(false)
    } else if op == G::INVERSE_SYMBOL {
        Some(true)
    } else {
        None
    }
}

impl<G> FromStr for GroupExpr<G>
where
    G: Group,
    MonoidElem<G>: FromLiteral,
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

    type Expr = GroupExpr<(Z, ZAdd)>;

    fn x() -> Expr {
        Expr::Symbol(Symbol::new("x"))
    }

    fn y() -> Expr {
        Expr::Symbol(Symbol::new("y"))
    }

    #[test]
    fn inverses_have_three_spellings() {
        let expected = Expr::Op(vec![x(), inverse(y())]);
        assert_eq!("x + inv(y)".parse::<Expr>().unwrap(), expected);
        assert_eq!("x + -y".parse::<Expr>().unwrap(), expected);
        assert_eq!("x - y".parse::<Expr>().unwrap(), expected);
    }

    #[test]
    fn spellings_come_from_the_operator() {
        type Mul = GroupExpr<(eqn_core::set::Q, crate::operator_impl::QMul)>;
        let (x, y) = (Mul::Symbol(Symbol::new("x")), Mul::Symbol(Symbol::new("y")));
        let expected = Mul::Op(vec![x.clone(), Mul::Inv(Box::new(y))]);
        assert_eq!("x / y".parse::<Mul>().unwrap(), expected);
        assert_eq!("x * /y".parse::<Mul>().unwrap(), expected);
        assert_eq!(
            "x + y".parse::<Mul>().unwrap_err(),
            ParseError::at(2, "unexpected `+`")
        );
        assert_eq!(
            "-x".parse::<Mul>().unwrap_err(),
            ParseError::new("group expressions have no `-` operator")
        );
        assert_eq!("-3".parse::<Mul>().unwrap(), Mul::Const((-3).into()));
        assert_eq!(
            "x^-1".parse::<Mul>().unwrap(),
            Mul::Pow {
                base: Box::new(x),
                exponent: -1
            }
        );
    }

    #[test]
    fn negative_literals_are_constants() {
        assert_eq!("-3".parse::<Expr>().unwrap(), Expr::Const(-3));
        assert_eq!("inv(3)".parse::<Expr>().unwrap(), inverse(Expr::Const(3)));
        assert_eq!("-(3)".parse::<Expr>().unwrap(), inverse(Expr::Const(3)));
    }

    #[test]
    fn powers_take_integer_exponents() {
        assert_eq!(
            "(x y)^-2".parse::<Expr>().unwrap(),
            Expr::Pow {
                base: Box::new(Expr::Op(vec![x(), y()])),
                exponent: -2,
            }
        );
        assert_eq!(
            "x^0".parse::<Expr>().unwrap(),
            Expr::Pow {
                base: Box::new(x()),
                exponent: 0,
            }
        );
        assert_eq!(
            "x^y".parse::<Expr>().unwrap_err(),
            ParseError::new("exponent must be an integer literal, found `y`")
        );
    }

    #[test]
    fn rejects_what_a_group_cannot_express() {
        assert_eq!(
            "x ∧ y".parse::<Expr>().unwrap_err(),
            ParseError::at(2, "unexpected `∧`")
        );
        assert_eq!(
            "inv(x, y)".parse::<Expr>().unwrap_err(),
            ParseError::new("unknown function `inv`")
        );
    }
}
