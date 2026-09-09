use std::str::FromStr;

use eqn_algebra::ring::{Ring, SemiRing};
use eqn_parser::{Ast, FromAst, Grammar, ParseError};

use crate::{DifferentialForm, Manifold, ZeroForm};

const WEDGE: &str = "∧";

/// The function ring's own syntax, extended with `∧` (parsed like the
/// ring's product) and the exterior derivative `d`, written `dx`, `d x`
/// or `d(...)`: `d` plus one character is `d` applied to that coordinate,
/// and a bare `d` applies to the factor that follows it. Any subtree
/// without `d` or `∧` is a 0-form and is read by the function ring, so
/// `x^2 + sin(y)` means whatever it means there. At the form level the
/// ring's declared sum, difference and product spellings are read as sum,
/// difference and wedge.
///
/// The product, juxtaposition and `∧` are all the wedge product, and
/// adjacent 0-form factors of one product are a single coefficient:
/// `2 x d(x)` is `(2x) ∧ dx`, as it reads on paper, not `2 ∧ x ∧ dx`.
impl<M> FromAst for DifferentialForm<M>
where
    M: Manifold,
    ZeroForm<M>: FromAst,
{
    fn grammar() -> Grammar {
        ZeroForm::<M>::grammar().alias(WEDGE, mul::<M>())
    }

    fn from_ast(ast: Ast) -> Result<Self, ParseError> {
        if !contains_form(&ast) {
            return ZeroForm::<M>::from_ast(ast).map(Self::Scalar);
        }
        match ast {
            Ast::Group(inner) => Self::from_ast(*inner),
            Ast::Prefix(op, inner) if op == sub::<M>() => {
                Ok(Self::Neg(Box::new(Self::from_ast(*inner)?)))
            }
            Ast::Infix(ref op, ..) if op == add::<M>() || op == sub::<M>() => ast
                .operands(sum::<M>)
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
            Ast::Infix(ref op, ..) if op == mul::<M>() || op == WEDGE => {
                let factors = ast
                    .operands(wedge::<M>)
                    .into_iter()
                    .map(|(_, factor)| factor);
                let mut out = Vec::new();
                for run in runs(differentials(factors)) {
                    out.push(match run {
                        Run::Scalars(scalars) => Self::from_ast(product::<M>(scalars))?,
                        Run::Form(form) => Self::from_ast(form)?,
                    });
                }
                Ok(match out.len() {
                    1 => out.pop().unwrap(),
                    _ => Self::Wedged(out),
                })
            }
            Ast::Infix(op, ..) | Ast::Prefix(op, _) | Ast::Postfix(op, _) => Err(ParseError::new(
                format!("differential forms have no `{op}` operator"),
            )),
            Ast::Call(name, mut args) if name == "d" && args.len() == 1 => Ok(Self::Differential(
                Box::new(Self::from_ast(args.pop().unwrap())?),
            )),
            Ast::Call(name, _) if name == "d" => {
                Err(ParseError::new("`d(ω)` takes one argument".to_owned()))
            }
            Ast::Ident(name) if name == "d" => Err(ParseError::new(
                "`d` is the exterior derivative; write `dx`, `d x` or `d(...)`".to_owned(),
            )),
            Ast::Ident(name) => {
                let x = coordinate(&name).expect("only `dx` idents are forms");
                Ok(Self::Differential(Box::new(Self::from_ast(Ast::Ident(
                    x.to_owned(),
                ))?)))
            }
            Ast::Call(..) | Ast::Number(_) => {
                unreachable!("only `d(...)` and `∧` make a subtree a form")
            }
        }
    }
}

/// `dx` -> `x`: the exterior derivative of a one-character coordinate.
/// Longer names starting with `d` (`delta`, `dx1`) stay ordinary symbols.
fn coordinate(ident: &str) -> Option<&str> {
    ident
        .strip_prefix('d')
        .filter(|rest| rest.chars().count() == 1)
}

/// Whether the subtree is a genuine form (contains `d`, `dx` or `∧`) rather
/// than a 0-form. A bare `d` counts, so it errors instead of becoming a
/// symbol.
fn contains_form(ast: &Ast) -> bool {
    match ast {
        Ast::Number(_) => false,
        Ast::Ident(name) => name == "d" || coordinate(name).is_some(),
        Ast::Call(name, args) => name == "d" || args.iter().any(contains_form),
        Ast::Group(inner) | Ast::Prefix(_, inner) | Ast::Postfix(_, inner) => contains_form(inner),
        Ast::Infix(op, ..) if op == WEDGE => true,
        Ast::Infix(_, lhs, rhs) => contains_form(lhs) || contains_form(rhs),
    }
}

fn add<M: Manifold>() -> &'static str {
    <M::Functions as SemiRing>::ADD_SYMBOL
}

fn sub<M: Manifold>() -> &'static str {
    <M::Functions as Ring>::SUB_SYMBOL
}

fn mul<M: Manifold>() -> &'static str {
    <M::Functions as SemiRing>::MUL_SYMBOL
}

fn sum<M: Manifold>(op: &str) -> Option<bool> {
    if op == add::<M>() {
        Some(false)
    } else if op == sub::<M>() {
        Some(true)
    } else {
        None
    }
}

fn wedge<M: Manifold>(op: &str) -> Option<bool> {
    (op == mul::<M>() || op == WEDGE).then_some(false)
}

/// Reads a bare `d` in a product as applying to the factor after it, so
/// `d x ∧ d y` is `d(x) ∧ d(y)`. A trailing `d` is left to error.
fn differentials(factors: impl Iterator<Item = Ast>) -> Vec<Ast> {
    let mut out = Vec::new();
    let mut pending = 0;
    for factor in factors {
        if factor == Ast::Ident("d".to_owned()) {
            pending += 1;
            continue;
        }
        let applied = (0..pending).fold(factor, |inner, _| Ast::Call("d".to_owned(), vec![inner]));
        out.push(applied);
        pending = 0;
    }
    out.extend((0..pending).map(|_| Ast::Ident("d".to_owned())));
    out
}

enum Run {
    Scalars(Vec<Ast>),
    Form(Ast),
}

/// Groups the factors of a product into maximal runs of 0-forms, each
/// becoming one coefficient, separated by the genuine forms.
fn runs(factors: Vec<Ast>) -> Vec<Run> {
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
fn product<M: Manifold>(mut scalars: Vec<Ast>) -> Ast {
    let first = scalars.remove(0);
    scalars.into_iter().fold(first, |acc, factor| {
        Ast::Infix(mul::<M>().to_owned(), Box::new(acc), Box::new(factor))
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
    fn differentials_have_three_spellings() {
        assert_eq!("dx".parse::<Form>().unwrap(), d(sc(x())));
        assert_eq!("d x".parse::<Form>().unwrap(), d(sc(x())));
        assert_eq!("d(x)".parse::<Form>().unwrap(), d(sc(x())));
        assert_eq!("d d x".parse::<Form>().unwrap(), d(d(sc(x()))));
        assert_eq!(
            "dθ".parse::<Form>().unwrap(),
            d(sc(Fun::Symbol(Symbol::new("θ"))))
        );

        // Only `d` plus one character is a differential; longer names are
        // symbols.
        for name in ["ddx", "delta", "dx1"] {
            assert_eq!(
                name.parse::<Form>().unwrap(),
                sc(Fun::Symbol(Symbol::new(name))),
                "{name}"
            );
        }

        // `d` takes the factor right after it; `^` binds tighter still.
        let expected = Form::Wedged(vec![sc(Fun::Mul(vec![c(2), x()])), d(sc(x())), d(sc(y()))]);
        assert_eq!("2 x dx dy".parse::<Form>().unwrap(), expected);
        assert_eq!("2 x d x ∧ d y".parse::<Form>().unwrap(), expected);
        assert_eq!(
            "d x^2 + dy".parse::<Form>().unwrap(),
            Form::Add(vec![d(sc("x^2".parse::<Fun>().unwrap())), d(sc(y())),])
        );
    }

    #[test]
    fn rejects_what_a_form_cannot_express() {
        for src in ["d", "x d", "d + x"] {
            assert_eq!(
                src.parse::<Form>().unwrap_err(),
                ParseError::new("`d` is the exterior derivative; write `dx`, `d x` or `d(...)`"),
                "{src}"
            );
        }
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
