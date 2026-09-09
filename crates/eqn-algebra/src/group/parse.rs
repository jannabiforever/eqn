use std::str::FromStr;

use eqn_core::symbol::Symbol;
use eqn_parser::{Assoc, Ast, FromAst, FromLiteral, Grammar, ParseError};

use super::{Group, GroupExpr};
use crate::monoid::MonoidElem;

/// `+`, `*` and juxtaposition denote the group operation; `-` and `/`
/// invert their right operand, prefix `-` and `inv(x)` invert, and `x^n`
/// takes any integer literal exponent. `x^-1` stays a [`GroupExpr::Pow`],
/// distinct from `inv(x)`.
impl<G> FromAst for GroupExpr<G>
where
    G: Group,
    MonoidElem<G>: FromLiteral,
{
    fn grammar() -> Grammar {
        Grammar::new()
            .infix("+", 1, Assoc::Left)
            .infix("-", 1, Assoc::Left)
            .infix("*", 2, Assoc::Left)
            .infix("/", 2, Assoc::Left)
            .juxtaposition("*")
            .prefix("-", 3)
            .infix("^", 4, Assoc::Right)
    }

    fn from_ast(ast: Ast) -> Result<Self, ParseError> {
        if let Some(text) = ast.literal("-") {
            return MonoidElem::<G>::from_literal(&text).map(Self::Const);
        }
        match ast {
            Ast::Ident(name) => Ok(Self::Symbol(Symbol::new(name))),
            Ast::Group(inner) => Self::from_ast(*inner),
            Ast::Prefix(_, inner) => Self::from_ast(*inner).map(inverse),
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
                .operands(operation)
                .into_iter()
                .map(|(inverted, operand)| {
                    let operand = Self::from_ast(operand)?;
                    Ok(if inverted { inverse(operand) } else { operand })
                })
                .collect::<Result<_, _>>()
                .map(Self::Op),
            Ast::Postfix(op, _) => Err(ParseError::new(format!(
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

fn operation(op: &str) -> Option<bool> {
    match op {
        "+" | "*" => Some(false),
        "-" | "/" => Some(true),
        _ => None,
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
        assert_eq!("x * inv(y)".parse::<Expr>().unwrap(), expected);
        assert_eq!("x + -y".parse::<Expr>().unwrap(), expected);
        assert_eq!("x - y".parse::<Expr>().unwrap(), expected);
        assert_eq!("x / y".parse::<Expr>().unwrap(), expected);
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
