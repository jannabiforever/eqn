use std::str::FromStr;

use eqn_algebra::ring::{Ring, SemiRing};
use eqn_parser::{Ast, FromAst, Grammar, ParseError};

use crate::{DifferentialForm, Manifold, WEDGE_SYMBOLS, ZeroForm};

/// The function ring's own syntax, extended with the wedge product `\wedge`
/// (spelled by its character or its LaTeX name and parsed like the ring's
/// product) and the exterior derivative `d`, written `dx`, `d x` or
/// `d(...)`: `d` plus one character is `d` applied to that coordinate, and a
/// bare `d` applies to the factor that follows it. Any subtree without `d`
/// or `\wedge` is a 0-form and is read by the function ring, so
/// `x^2 + sin(y)` means whatever it means there. At the form level the
/// ring's declared sum, difference and product spellings are read as sum,
/// difference and wedge.
///
/// The product, juxtaposition and `\wedge` are all the wedge product, and
/// adjacent 0-form factors of one product are a single coefficient:
/// `2 x d(x)` is `(2x) \wedge dx`, as it reads on paper, not
/// `2 \wedge x \wedge dx`.
impl<M> FromAst for DifferentialForm<M>
where
    M: Manifold,
    ZeroForm<M>: FromAst,
{
    fn grammar() -> anyhow::Result<Grammar> {
        WEDGE_SYMBOLS
            .iter()
            .try_fold(ZeroForm::<M>::grammar()?, |grammar, wedge| {
                grammar.alias(wedge, Self::MUL)
            })
    }

    fn from_ast(ast: Ast) -> Result<Self, ParseError> {
        if !Self::contains_form(&ast) {
            return ZeroForm::<M>::from_ast(ast).map(Self::Scalar);
        }
        match ast {
            Ast::Group(inner) => Self::from_ast(*inner),
            Ast::Prefix(op, inner) if op == Self::SUB => {
                Ok(Self::Neg(Box::new(Self::from_ast(*inner)?)))
            }
            Ast::Infix(ref op, ..) if op == Self::ADD || op == Self::SUB => ast
                .operands(Self::sum)
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
            Ast::Infix(ref op, ..) if Self::wedge(op).is_some() => {
                let factors = ast
                    .operands(Self::wedge)
                    .into_iter()
                    .map(|(_, factor)| factor);
                let mut forms = Self::coefficients(Self::differentials(factors))
                    .into_iter()
                    .map(Self::from_ast)
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(match forms.len() {
                    1 => forms.pop().unwrap(),
                    _ => Self::Wedged(forms),
                })
            }
            Ast::Infix(op, ..) | Ast::Prefix(op, _) | Ast::Postfix(op, _) => Err(ParseError::new(
                format!("differential forms have no `{op}` operator"),
            )),
            Ast::Call(name, mut args) if name == "d" && args.len() == 1 => Ok(Self::Differential(
                Box::new(Self::from_ast(args.pop().unwrap())?),
            )),
            Ast::Call(name, args) if name == "d" => Err(ParseError::new(format!(
                "`d` takes one argument, found {}",
                args.len()
            ))),
            Ast::Ident(name) if name == "d" => Err(ParseError::new(
                "`d` is the exterior derivative; write `dx`, `d x` or `d(...)`".to_owned(),
            )),
            Ast::Ident(name) => {
                let x = Self::coordinate(&name).expect("only `dx` idents are forms");
                Ok(Self::Differential(Box::new(Self::from_ast(Ast::Ident(
                    x.to_owned(),
                ))?)))
            }
            Ast::Call(..) | Ast::Number(_) => {
                unreachable!("only `d(...)` and `\\wedge` make a subtree a form")
            }
        }
    }
}

impl<M: Manifold> DifferentialForm<M> {
    const ADD: &'static str = <M::Functions as SemiRing>::ADD_SYMBOL;
    const SUB: &'static str = <M::Functions as Ring>::SUB_SYMBOL;
    const MUL: &'static str = <M::Functions as SemiRing>::MUL_SYMBOL;

    /// `dx` -> `x`: the exterior derivative of a one-character coordinate.
    /// Longer names starting with `d` (`delta`, `dx1`) stay ordinary symbols.
    fn coordinate(ident: &str) -> Option<&str> {
        ident
            .strip_prefix('d')
            .filter(|rest| rest.chars().count() == 1)
    }

    /// Whether the subtree is a genuine form (contains `d`, `dx` or `\wedge`)
    /// rather than a 0-form. A bare `d` counts, so it errors instead of
    /// becoming a symbol.
    fn contains_form(ast: &Ast) -> bool {
        match ast {
            Ast::Number(_) => false,
            Ast::Ident(name) => name == "d" || Self::coordinate(name).is_some(),
            Ast::Call(name, args) => name == "d" || args.iter().any(Self::contains_form),
            Ast::Group(inner) | Ast::Prefix(_, inner) | Ast::Postfix(_, inner) => {
                Self::contains_form(inner)
            }
            Ast::Infix(op, ..) if WEDGE_SYMBOLS.contains(&op.as_str()) => true,
            Ast::Infix(_, lhs, rhs) => Self::contains_form(lhs) || Self::contains_form(rhs),
        }
    }

    /// Classifies `op` for [`Ast::operands`]: a sum continues through the
    /// ring's addition, and through its subtraction with the term negated.
    fn sum(op: &str) -> Option<bool> {
        if op == Self::ADD {
            Some(false)
        } else if op == Self::SUB {
            Some(true)
        } else {
            None
        }
    }

    /// Classifies `op` for [`Ast::operands`]: the ring's product and every
    /// spelling of `\wedge` continue one wedge product.
    fn wedge(op: &str) -> Option<bool> {
        (op == Self::MUL || WEDGE_SYMBOLS.contains(&op)).then_some(false)
    }

    /// Reads a bare `d` in a product as applying to the factor after it, so
    /// `d x \wedge d y` is `d(x) \wedge d(y)`. A trailing `d` is left to
    /// error.
    fn differentials(factors: impl Iterator<Item = Ast>) -> Vec<Ast> {
        let mut out = Vec::new();
        let mut pending = 0;
        for factor in factors {
            if factor == Ast::Ident("d".to_owned()) {
                pending += 1;
                continue;
            }
            let applied =
                (0..pending).fold(factor, |inner, _| Ast::Call("d".to_owned(), vec![inner]));
            out.push(applied);
            pending = 0;
        }
        out.extend((0..pending).map(|_| Ast::Ident("d".to_owned())));
        out
    }

    /// Merges each maximal run of adjacent 0-form factors into one product,
    /// so that the function ring lowers it as a single coefficient; genuine
    /// forms pass through.
    fn coefficients(factors: Vec<Ast>) -> Vec<Ast> {
        let mut out = Vec::new();
        let mut scalars = Vec::new();
        for factor in factors {
            if Self::contains_form(&factor) {
                out.extend(Self::product(std::mem::take(&mut scalars)));
                out.push(factor);
            } else {
                scalars.push(factor);
            }
        }
        out.extend(Self::product(scalars));
        out
    }

    /// The left-nested product of `scalars` in the ring's spelling, or
    /// nothing when there are none.
    fn product(scalars: Vec<Ast>) -> Option<Ast> {
        scalars
            .into_iter()
            .reduce(|acc, factor| Ast::Infix(Self::MUL.to_owned(), Box::new(acc), Box::new(factor)))
    }
}

impl<M> FromStr for DifferentialForm<M>
where
    M: Manifold,
    ZeroForm<M>: FromAst,
{
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
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

    fn error(src: &str) -> ParseError {
        src.parse::<Form>().unwrap_err().downcast().unwrap()
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
        assert_eq!(r"2 x \wedge d(x)".parse::<Form>().unwrap(), expected);
        assert_eq!(r"2 \wedge x \wedge d(x)".parse::<Form>().unwrap(), expected);

        // Coefficients can sit anywhere, and a lone scalar run is not wedged.
        assert_eq!(
            "d(x) y d(y)".parse::<Form>().unwrap(),
            Form::Wedged(vec![d(sc(x())), sc(y()), d(sc(y()))])
        );
        assert_eq!(
            r"x \wedge y".parse::<Form>().unwrap(),
            sc(Fun::Mul(vec![x(), y()]))
        );
    }

    #[test]
    fn the_wedge_has_two_spellings() {
        let expected = Form::Wedged(vec![d(sc(x())), d(sc(y()))]);
        assert_eq!(r"dx \wedge dy".parse::<Form>().unwrap(), expected);
        assert_eq!("dx \u{2227} dy".parse::<Form>().unwrap(), expected);
    }

    #[test]
    fn sums_negations_and_groups_lower_structurally() {
        assert_eq!(
            "y d(x) - x d(y) + -d(d(x))".parse::<Form>().unwrap(),
            Form::Add(vec![
                Form::Wedged(vec![sc(y()), d(sc(x()))]),
                Form::Neg(Box::new(Form::Wedged(vec![sc(x()), d(sc(y()))]))),
                Form::Neg(Box::new(d(d(sc(x()))))),
            ])
        );
        assert_eq!(
            r"2 \wedge (x + d(y)) \wedge d(x)".parse::<Form>().unwrap(),
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
        // `d\theta`: one character, not one byte.
        assert_eq!(
            "d\u{3b8}".parse::<Form>().unwrap(),
            d(sc(Fun::Symbol(Symbol::new("\u{3b8}"))))
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
        assert_eq!(r"2 x d x \wedge d y".parse::<Form>().unwrap(), expected);
        assert_eq!(
            "d x^2 + dy".parse::<Form>().unwrap(),
            Form::Add(vec![d(sc("x^2".parse::<Fun>().unwrap())), d(sc(y())),])
        );
    }

    #[test]
    fn rejects_what_a_form_cannot_express() {
        for src in ["d", "x d", "d + x"] {
            assert_eq!(
                error(src),
                ParseError::new("`d` is the exterior derivative; write `dx`, `d x` or `d(...)`"),
                "{src}"
            );
        }
        assert_eq!(
            error("d(x, y)"),
            ParseError::new("`d` takes one argument, found 2")
        );
        assert_eq!(
            error("d(x) / x"),
            ParseError::new("differential forms have no `/` operator")
        );
        assert_eq!(
            error("d(x)^2"),
            ParseError::new("differential forms have no `^` operator")
        );
    }
}
