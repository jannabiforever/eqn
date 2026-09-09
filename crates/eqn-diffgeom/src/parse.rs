use std::str::FromStr;

use eqn_parser::{Ast, BinaryOp, FromAst, ParseError, UnaryOp};

use crate::{DifferentialForm, Manifold, ZeroForm};

/// Forms are built from 0-forms with `+`, `-`, `∧` and `d(...)`, the
/// exterior derivative. Any subtree without `d` or `∧` is a 0-form and is
/// read by the manifold's function ring, so `x^2 + sin(y)` means whatever it
/// means there.
///
/// `*`, juxtaposition and `∧` are all the wedge product, and adjacent
/// 0-form factors of one product are a single coefficient: `2 x d(x)` is
/// `(2x) ∧ dx`, as it reads on paper, not `2 ∧ x ∧ dx`.
impl<M> FromAst for DifferentialForm<M>
where
    M: Manifold,
    ZeroForm<M>: FromAst,
{
    fn from_ast(ast: Ast) -> Result<Self, ParseError> {
        if !contains_form(&ast) {
            return ZeroForm::<M>::from_ast(ast).map(Self::Scalar);
        }
        match ast {
            Ast::Group(inner) => Self::from_ast(*inner),
            Ast::Unary(UnaryOp::Neg, inner) => Ok(Self::Neg(Box::new(Self::from_ast(*inner)?))),
            Ast::Binary(BinaryOp::Add | BinaryOp::Sub, ..) => ast
                .operands(sum)
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
            Ast::Binary(BinaryOp::Mul | BinaryOp::Wedge, ..) => {
                let factors = ast.operands(wedge).into_iter().map(|(_, factor)| factor);
                let mut out = Vec::new();
                for run in runs(factors) {
                    out.push(match run {
                        Run::Scalars(scalars) => Self::from_ast(product(scalars))?,
                        Run::Form(form) => Self::from_ast(form)?,
                    });
                }
                Ok(match out.len() {
                    1 => out.pop().unwrap(),
                    _ => Self::Wedged(out),
                })
            }
            Ast::Binary(op, ..) => Err(ParseError::new(format!(
                "differential forms have no `{op}` operator"
            ))),
            Ast::Call(name, mut args) if name == "d" && args.len() == 1 => Ok(Self::Differential(
                Box::new(Self::from_ast(args.pop().unwrap())?),
            )),
            Ast::Call(name, _) if name == "d" => {
                Err(ParseError::new("`d(ω)` takes one argument".to_owned()))
            }
            Ast::Ident(name) => Err(ParseError::new(format!(
                "`{name}` is the exterior derivative; write `{name}(...)`"
            ))),
            Ast::Call(..) | Ast::Number(_) => {
                unreachable!("only `d(...)` and `∧` make a subtree a form")
            }
        }
    }
}

/// Whether the subtree is a genuine form (contains `d(...)` or `∧`) rather
/// than a 0-form. A bare `d` counts, so it errors instead of becoming a
/// symbol.
fn contains_form(ast: &Ast) -> bool {
    match ast {
        Ast::Number(_) => false,
        Ast::Ident(name) => name == "d",
        Ast::Call(name, args) => name == "d" || args.iter().any(contains_form),
        Ast::Group(inner) | Ast::Unary(_, inner) => contains_form(inner),
        Ast::Binary(BinaryOp::Wedge, ..) => true,
        Ast::Binary(_, lhs, rhs) => contains_form(lhs) || contains_form(rhs),
    }
}

fn sum(op: BinaryOp) -> Option<bool> {
    match op {
        BinaryOp::Add => Some(false),
        BinaryOp::Sub => Some(true),
        _ => None,
    }
}

fn wedge(op: BinaryOp) -> Option<bool> {
    matches!(op, BinaryOp::Mul | BinaryOp::Wedge).then_some(false)
}

enum Run {
    Scalars(Vec<Ast>),
    Form(Ast),
}

/// Groups the factors of a product into maximal runs of 0-forms, each
/// becoming one coefficient, separated by the genuine forms.
fn runs(factors: impl Iterator<Item = Ast>) -> Vec<Run> {
    let mut runs = Vec::new();
    for factor in factors {
        if contains_form(&factor) {
            runs.push(Run::Form(factor));
        } else if let Some(Run::Scalars(scalars)) = runs.last_mut() {
            scalars.push(factor);
        } else {
            runs.push(Run::Scalars(vec![factor]));
        }
    }
    runs
}

/// Rebuilds a left-nested product for the function ring to lower.
fn product(mut scalars: Vec<Ast>) -> Ast {
    let first = scalars.remove(0);
    scalars.into_iter().fold(first, |acc, factor| {
        Ast::Binary(BinaryOp::Mul, Box::new(acc), Box::new(factor))
    })
}

impl<M> FromStr for DifferentialForm<M>
where
    M: Manifold,
    ZeroForm<M>: FromAst,
{
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        eqn_parser::parse(s)
    }
}

#[cfg(test)]
mod tests {
    use eqn_algebra::operator_impl::{QAdd, QMul};
    use eqn_analysis::ElementaryExpr;
    use eqn_core::set::{Q, Rational};
    use eqn_core::symbol::Symbol;

    use super::*;
    use crate::tests::Plane;

    type Form = DifferentialForm<Plane>;
    type Fun = ElementaryExpr<(Q, QAdd, QMul)>;

    fn c(i: i64) -> Fun {
        Fun::Const(Rational::from(i))
    }

    fn x() -> Fun {
        Fun::Symbol(Symbol::new("x"))
    }

    fn y() -> Fun {
        Fun::Symbol(Symbol::new("y"))
    }

    fn sc(f: Fun) -> Form {
        Form::Scalar(f)
    }

    fn d(form: Form) -> Form {
        Form::Differential(Box::new(form))
    }

    #[test]
    fn zero_forms_are_read_by_the_function_ring() {
        assert_eq!(
            "x^2 + sin(y)".parse::<Form>().unwrap(),
            sc("x^2 + sin(y)".parse::<Fun>().unwrap())
        );
        assert_eq!("(x)".parse::<Form>().unwrap(), sc(x()));
    }

    #[test]
    fn adjacent_scalar_factors_form_one_coefficient() {
        let expected = Form::Wedged(vec![sc(Fun::Mul(vec![c(2), x()])), d(sc(x()))]);
        assert_eq!("2 x d(x)".parse::<Form>().unwrap(), expected);
        assert_eq!("2 * x * d(x)".parse::<Form>().unwrap(), expected);
        assert_eq!("2 x ∧ d(x)".parse::<Form>().unwrap(), expected);
        assert_eq!("2 ∧ x ∧ d(x)".parse::<Form>().unwrap(), expected);

        // Coefficients can sit anywhere, and a lone scalar run is not wedged.
        assert_eq!(
            "d(x) y d(y)".parse::<Form>().unwrap(),
            Form::Wedged(vec![d(sc(x())), sc(y()), d(sc(y()))])
        );
        assert_eq!(
            "x ∧ y".parse::<Form>().unwrap(),
            sc(Fun::Mul(vec![x(), y()]))
        );
    }

    #[test]
    fn sums_negation_and_nesting() {
        assert_eq!(
            "y d(x) - x d(y) + -d(d(x))".parse::<Form>().unwrap(),
            Form::Add(vec![
                Form::Wedged(vec![sc(y()), d(sc(x()))]),
                Form::Neg(Box::new(Form::Wedged(vec![sc(x()), d(sc(y()))]))),
                Form::Neg(Box::new(d(d(sc(x()))))),
            ])
        );
        assert_eq!(
            "2 ∧ (x + d(y)) ∧ d(x)".parse::<Form>().unwrap(),
            Form::Wedged(vec![
                sc(c(2)),
                Form::Add(vec![sc(x()), d(sc(y()))]),
                d(sc(x())),
            ])
        );
    }

    #[test]
    fn rejects_what_a_form_cannot_express() {
        assert_eq!(
            "d x".parse::<Form>().unwrap_err(),
            ParseError::new("`d` is the exterior derivative; write `d(...)`")
        );
        assert_eq!(
            "d(x, y)".parse::<Form>().unwrap_err(),
            ParseError::new("`d(ω)` takes one argument")
        );
        assert_eq!(
            "d(x) / x".parse::<Form>().unwrap_err(),
            ParseError::new("differential forms have no `/` operator")
        );
        assert_eq!(
            "d(x)^2".parse::<Form>().unwrap_err(),
            ParseError::new("differential forms have no `^` operator")
        );
    }
}
