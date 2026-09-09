use std::str::FromStr;

use eqn_algebra::field::Field;
use eqn_algebra::ring::RingElem;
use eqn_core::symbol::Symbol;
use eqn_parser::{Assoc, Ast, FromAst, FromLiteral, Grammar, ParseError};

use crate::{Elementary, ElementaryExpr};

/// The field's own arithmetic spellings
/// ([`eqn_algebra::ring::SemiRing::ADD_SYMBOL`] and friends, `+ - * /` for the
/// rationals) with `^n` for any integer literal `n`; `a / b` is `a * b^-1`. The
/// functions are `exp`, `log`, `sin`, `cos`, and `D(f, x)` is the unevaluated
/// derivative of `f` with respect to `x`.
impl<F> FromAst for ElementaryExpr<F>
where
    F: Field,
    RingElem<F>: FromLiteral,
{
    fn grammar() -> Grammar {
        Grammar::new()
            .infix(F::ADD_SYMBOL, 1, Assoc::Left)
            .infix(F::SUB_SYMBOL, 1, Assoc::Left)
            .infix(F::MUL_SYMBOL, 2, Assoc::Left)
            .infix(F::DIV_SYMBOL, 2, Assoc::Left)
            .juxtaposition(F::MUL_SYMBOL)
            .prefix("-", 3)
            .prefix(F::SUB_SYMBOL, 3)
            .infix("^", 4, Assoc::Right)
    }

    fn from_ast(ast: Ast) -> Result<Self, ParseError> {
        if let Some(text) = ast.literal("-") {
            return RingElem::<F>::from_literal(&text).map(Self::Const);
        }
        match ast {
            Ast::Ident(name) if function(&name).is_some() || name == "D" => Err(ParseError::new(
                format!("`{name}` is a function; write `{name}(...)`"),
            )),
            Ast::Ident(name) => Ok(Self::Symbol(Symbol::new(name))),
            Ast::Group(inner) => Self::from_ast(*inner),
            Ast::Prefix(op, inner) if op == F::SUB_SYMBOL => {
                Ok(Self::Neg(Box::new(Self::from_ast(*inner)?)))
            }
            Ast::Infix(ref op, ..) if op == F::ADD_SYMBOL || op == F::SUB_SYMBOL => ast
                .operands(sum::<F>)
                .into_iter()
                .map(|(negated, term)| {
                    let term = Self::from_ast(term)?;
                    Ok(if negated {
                        Self::Neg(Box::new(term))
                    } else {
                        term
                    })
                })
                .collect::<Result<_, _>>()
                .map(Self::Add),
            Ast::Infix(ref op, ..) if op == F::MUL_SYMBOL || op == F::DIV_SYMBOL => ast
                .operands(product::<F>)
                .into_iter()
                .map(|(divided, factor)| {
                    let factor = Self::from_ast(factor)?;
                    Ok(if divided {
                        Self::Pow {
                            base: Box::new(factor),
                            exponent: -1,
                        }
                    } else {
                        factor
                    })
                })
                .collect::<Result<_, _>>()
                .map(Self::Mul),
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
            Ast::Infix(op, ..) | Ast::Prefix(op, _) | Ast::Postfix(op, _) => Err(ParseError::new(
                format!("elementary expressions have no `{op}` operator"),
            )),
            Ast::Call(name, args) => call(name, args),
            Ast::Number(_) => unreachable!("literals are handled above"),
        }
    }
}

fn sum<F: Field>(op: &str) -> Option<bool> {
    if op == F::ADD_SYMBOL {
        Some(false)
    } else if op == F::SUB_SYMBOL {
        Some(true)
    } else {
        None
    }
}

fn product<F: Field>(op: &str) -> Option<bool> {
    if op == F::MUL_SYMBOL {
        Some(false)
    } else if op == F::DIV_SYMBOL {
        Some(true)
    } else {
        None
    }
}

fn function(name: &str) -> Option<Elementary> {
    match name {
        "exp" => Some(Elementary::Exp),
        "log" => Some(Elementary::Log),
        "sin" => Some(Elementary::Sin),
        "cos" => Some(Elementary::Cos),
        _ => None,
    }
}

fn call<F>(name: String, mut args: Vec<Ast>) -> Result<ElementaryExpr<F>, ParseError>
where
    F: Field,
    RingElem<F>: FromLiteral,
{
    if let Some(kind) = function(&name) {
        if args.len() != 1 {
            return Err(ParseError::new(format!(
                "`{name}` takes one argument, found {}",
                args.len()
            )));
        }
        let arg = ElementaryExpr::from_ast(args.pop().unwrap())?;
        return Ok(ElementaryExpr::elementary(kind, arg));
    }
    if name != "D" {
        return Err(ParseError::new(format!("unknown function `{name}`")));
    }
    if args.len() != 2 {
        return Err(ParseError::new(format!(
            "`D(f, x)` takes two arguments, found {}",
            args.len()
        )));
    }
    let wrt = match args.pop().unwrap() {
        Ast::Ident(wrt) => Symbol::new(wrt),
        other => {
            return Err(ParseError::new(format!(
                "`D` differentiates with respect to a symbol, found `{other}`"
            )));
        }
    };
    let inner = ElementaryExpr::from_ast(args.pop().unwrap())?;
    Ok(ElementaryExpr::d(wrt, inner))
}

impl<F> FromStr for ElementaryExpr<F>
where
    F: Field,
    RingElem<F>: FromLiteral,
{
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        eqn_parser::parse(s)
    }
}

#[cfg(test)]
mod tests {
    use eqn_algebra::operator_impl::{QAdd, QMul};
    use eqn_core::set::{Q, Rational};

    use super::*;

    type Expr = ElementaryExpr<(Q, QAdd, QMul)>;

    fn c(i: i64) -> Expr {
        Expr::Const(Rational::from(i))
    }

    fn x() -> Expr {
        Expr::Symbol(Symbol::new("x"))
    }

    fn pow(base: Expr, exponent: isize) -> Expr {
        Expr::Pow {
            base: Box::new(base),
            exponent,
        }
    }

    #[test]
    fn arithmetic_lowers_structurally() {
        assert_eq!(
            "1 - 2x / (x + 1)^-2".parse::<Expr>().unwrap(),
            Expr::Add(vec![
                c(1),
                Expr::Neg(Box::new(Expr::Mul(vec![
                    c(2),
                    x(),
                    pow(pow(Expr::Add(vec![x(), c(1)]), -2), -1),
                ]))),
            ])
        );
        assert_eq!("-3".parse::<Expr>().unwrap(), c(-3));
        assert_eq!("-x".parse::<Expr>().unwrap(), Expr::Neg(Box::new(x())));
    }

    #[test]
    fn functions_and_derivatives() {
        assert_eq!(
            "2 exp(log(x)) sin(x)^2".parse::<Expr>().unwrap(),
            Expr::Mul(vec![
                c(2),
                Expr::elementary(Elementary::Exp, Expr::elementary(Elementary::Log, x())),
                pow(Expr::elementary(Elementary::Sin, x()), 2),
            ])
        );
        assert_eq!(
            "D(cos(x), x)".parse::<Expr>().unwrap(),
            Expr::d(Symbol::new("x"), Expr::elementary(Elementary::Cos, x()))
        );
    }

    #[test]
    fn rejects_misused_functions() {
        assert_eq!(
            "sin x".parse::<Expr>().unwrap_err(),
            ParseError::new("`sin` is a function; write `sin(...)`")
        );
        assert_eq!(
            "sin(x, y)".parse::<Expr>().unwrap_err(),
            ParseError::new("`sin` takes one argument, found 2")
        );
        assert_eq!(
            "D(x)".parse::<Expr>().unwrap_err(),
            ParseError::new("`D(f, x)` takes two arguments, found 1")
        );
        assert_eq!(
            "D(x, 2)".parse::<Expr>().unwrap_err(),
            ParseError::new("`D` differentiates with respect to a symbol, found `2`")
        );
        assert_eq!(
            "tan(x)".parse::<Expr>().unwrap_err(),
            ParseError::new("unknown function `tan`")
        );
        assert_eq!(
            "x ∧ y".parse::<Expr>().unwrap_err(),
            ParseError::at(2, "unexpected `∧`")
        );
        assert_eq!(
            "x^y".parse::<Expr>().unwrap_err(),
            ParseError::new("exponent must be an integer literal, found `y`")
        );
    }
}
