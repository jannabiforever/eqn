use eqn_algebra::field::Field;
use eqn_algebra::ring::RingElem;
use eqn_core::rewriter::Rewriter;
use eqn_core::symbol::Symbol;

use crate::{Elementary, ElementaryExpr};

// ================================================================================
// Normalization engine
// ================================================================================

/// A single factor of a term: a symbol, an elementary function applied to a
/// (normalized) argument, or a normalized sum raised to a negative power
/// (e.g. the `(x + 1)` in `(x + 1)^-1`).
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq)]
enum Atom<F: Field> {
    Symbol(Symbol<F::Domain>),
    Fn(Elementary, ElementaryExpr<F>),
    Sum(ElementaryExpr<F>),
}

impl<F: Field> Atom<F> {
    fn into_expr(self) -> ElementaryExpr<F> {
        match self {
            Atom::Symbol(s) => ElementaryExpr::Symbol(s),
            Atom::Fn(k, a) => ElementaryExpr::Fn(k, Box::new(a)),
            Atom::Sum(e) => e,
        }
    }
}

struct Term<F: Field> {
    coeff: RingElem<F>,
    factors: Vec<(Atom<F>, isize)>,
}

impl<F: Field> Term<F> {
    fn one() -> Self {
        Self {
            coeff: F::ONE,
            factors: vec![],
        }
    }

    fn negated(mut self) -> Self {
        self.coeff = F::negate(self.coeff);
        self
    }

    fn mul(&self, other: &Self) -> Self {
        Self {
            coeff: F::multiply(self.coeff.clone(), other.coeff.clone()),
            factors: self.factors.iter().chain(&other.factors).cloned().collect(),
        }
    }

    fn into_expr(self) -> ElementaryExpr<F> {
        let mut factors: Vec<ElementaryExpr<F>> = self
            .factors
            .into_iter()
            .map(|(atom, e)| {
                let base = atom.into_expr();
                if e == 1 {
                    base
                } else {
                    ElementaryExpr::Pow {
                        base: Box::new(base),
                        exponent: e,
                    }
                }
            })
            .collect();
        if factors.is_empty() || self.coeff != F::ONE {
            factors.insert(0, ElementaryExpr::Const(self.coeff));
        }
        match factors.len() {
            1 => factors.pop().unwrap(),
            _ => ElementaryExpr::Mul(factors),
        }
    }
}

/// Structural order used for canonical sorting. Never compares domain
/// elements: constants tie (at most one constant survives folding within a
/// term, so the tie is harmless), which keeps `Ord` off the domain.
fn cmp_structural<F: Field>(a: &ElementaryExpr<F>, b: &ElementaryExpr<F>) -> std::cmp::Ordering {
    use std::cmp::Ordering;

    use ElementaryExpr::*;

    const fn rank<F: Field>(e: &ElementaryExpr<F>) -> u8 {
        match e {
            Const(_) => 0,
            Symbol(_) => 1,
            Pow { .. } => 2,
            Fn(_, _) => 3,
            Mul(_) => 4,
            Add(_) => 5,
            Neg(_) => 6,
            D { .. } => 7,
        }
    }

    match (a, b) {
        (Const(_), Const(_)) => Ordering::Equal,
        (Symbol(s), Symbol(o)) => s.cmp(o),
        (
            Pow {
                base: sb,
                exponent: se,
            },
            Pow {
                base: ob,
                exponent: oe,
            },
        ) => cmp_structural(sb, ob).then(se.cmp(oe)),
        (Fn(sk, sa), Fn(ok, oa)) => sk.cmp(ok).then_with(|| cmp_structural(sa, oa)),
        (Mul(s), Mul(o)) | (Add(s), Add(o)) => s
            .iter()
            .zip(o)
            .map(|(i, j)| cmp_structural(i, j))
            .find(|c| *c != Ordering::Equal)
            .unwrap_or(s.len().cmp(&o.len())),
        (Neg(s), Neg(o)) => cmp_structural(s, o),
        (D { wrt: sw, inner: si }, D { wrt: ow, inner: oi }) => {
            sw.cmp(ow).then_with(|| cmp_structural(si, oi))
        }
        (a, b) => rank(a).cmp(&rank(b)),
    }
}

/// Structural order over atoms: symbols by name, functions by kind then
/// argument, sums structurally. Ties (e.g. two `Sum`s whose constants
/// happen to be at the same structural position) are broken by insertion
/// order in [`canonical`]; merging uses `==`, never this comparator.
fn cmp_atom<F: Field>(a: &Atom<F>, b: &Atom<F>) -> std::cmp::Ordering {
    const fn rank<F: Field>(a: &Atom<F>) -> u8 {
        match a {
            Atom::Symbol(_) => 0,
            Atom::Fn(_, _) => 1,
            Atom::Sum(_) => 2,
        }
    }

    match (a, b) {
        (Atom::Symbol(s), Atom::Symbol(o)) => s.cmp(o),
        (Atom::Fn(sk, sa), Atom::Fn(ok, oa)) => sk.cmp(ok).then_with(|| cmp_structural(sa, oa)),
        (Atom::Sum(s), Atom::Sum(o)) => cmp_structural(s, o),
        (a, b) => rank(a).cmp(&rank(b)),
    }
}

/// Lexicographic order over a term's factor list: `cmp_atom` on each atom,
/// then the exponent, then length.
fn cmp_term<F: Field>(a: &Term<F>, b: &Term<F>) -> std::cmp::Ordering {
    use std::cmp::Ordering;

    a.factors
        .iter()
        .zip(&b.factors)
        .map(|((aa, ae), (ba, be))| cmp_atom(aa, ba).then(ae.cmp(be)))
        .find(|c| *c != Ordering::Equal)
        .unwrap_or(a.factors.len().cmp(&b.factors.len()))
}

/// Expands the tree into its term list: linearity, `Mul` cartesian product,
/// integer powers, elementary-function constant folding and `exp∘log`
/// cancellation, and `D` via [`derivative`]. The result is not yet sorted or
/// merged; that is [`canonical`]'s job.
fn terms<F: Field>(expr: ElementaryExpr<F>) -> Vec<Term<F>> {
    match expr {
        ElementaryExpr::Const(c) => vec![Term {
            coeff: c,
            factors: vec![],
        }],
        ElementaryExpr::Symbol(s) => vec![Term {
            coeff: F::ONE,
            factors: vec![(Atom::Symbol(s), 1)],
        }],
        ElementaryExpr::Neg(x) => terms(*x).into_iter().map(Term::negated).collect(),
        ElementaryExpr::Add(xs) => xs.into_iter().flat_map(terms).collect(),
        ElementaryExpr::Mul(xs) => xs.into_iter().fold(vec![Term::one()], |acc, x| {
            let rhs = terms(x);
            acc.iter()
                .flat_map(|a| rhs.iter().map(move |b| a.mul(b)))
                .collect()
        }),
        ElementaryExpr::Pow { base, exponent } => pow_terms(*base, exponent),
        ElementaryExpr::Fn(kind, arg) => fn_terms(kind, *arg),
        ElementaryExpr::D { wrt, inner } => terms(derivative(*inner, &wrt)),
    }
}

/// `base^n` as a term list. `n == 0` is one; `n > 0` is repeated
/// multiplication; `n < 0` inverts (single-term base only -- a genuine sum
/// stays an opaque [`Atom::Sum`] factor, since a field has no general
/// `(a + b)^-1` law). Panics if `base` normalizes to zero, matching
/// [`Field::invert`]'s contract on `ZERO`.
fn pow_terms<F: Field>(base: ElementaryExpr<F>, n: isize) -> Vec<Term<F>> {
    let b = canonical(terms(base));

    if n == 0 {
        return vec![Term::one()];
    }
    if n > 0 {
        let mut acc = vec![Term::one()];
        for _ in 0..n {
            acc = acc
                .iter()
                .flat_map(|a| b.iter().map(move |c| a.mul(c)))
                .collect();
        }
        return acc;
    }

    match b.as_slice() {
        [] => panic!("division by zero"),
        [t] => {
            let inv = F::invert(t.coeff.clone());
            let mut coeff = F::ONE;
            for _ in 0..n.unsigned_abs() {
                coeff = F::multiply(coeff, inv.clone());
            }
            let factors: Vec<(Atom<F>, isize)> =
                t.factors.iter().map(|(a, e)| (a.clone(), e * n)).collect();
            let term = Term { coeff, factors };
            // A Sum atom must only ever carry a negative exponent; negating
            // n here can flip an already-negative Sum exponent positive
            // (e.g. inverting (x+1)^-1), so re-expand instead of keeping it
            // as an opaque atom.
            if term
                .factors
                .iter()
                .any(|(a, e)| matches!(a, Atom::Sum(_)) && *e > 0)
            {
                terms(term.into_expr())
            } else {
                vec![term]
            }
        }
        _ => vec![Term {
            coeff: F::ONE,
            factors: vec![(Atom::Sum(build_sum(b)), n)],
        }],
    }
}

/// `kind(arg)` as a term list: folds the four boundary values
/// (`exp 0 = 1`, `log 1 = 0`, `sin 0 = 0`, `cos 0 = 1`) and cancels
/// `exp∘log` and `log∘exp`; otherwise stays one opaque [`Atom::Fn`] factor.
fn fn_terms<F: Field>(kind: Elementary, arg: ElementaryExpr<F>) -> Vec<Term<F>> {
    use Elementary::{Cos, Exp, Log, Sin};

    let a = build_sum(canonical(terms(arg)));
    match (kind, a) {
        (Exp, ElementaryExpr::Const(c)) if c == F::ZERO => vec![Term::one()],
        (Log, ElementaryExpr::Const(c)) if c == F::ONE => vec![Term {
            coeff: F::ZERO,
            factors: vec![],
        }],
        (Sin, ElementaryExpr::Const(c)) if c == F::ZERO => vec![Term {
            coeff: F::ZERO,
            factors: vec![],
        }],
        (Cos, ElementaryExpr::Const(c)) if c == F::ZERO => vec![Term::one()],
        (Exp, ElementaryExpr::Fn(Log, u)) => terms(*u),
        (Log, ElementaryExpr::Fn(Exp, u)) => terms(*u),
        (k, a) => vec![Term {
            coeff: F::ONE,
            factors: vec![(Atom::Fn(k, a), 1)],
        }],
    }
}

/// Symbolic differentiation on the raw tree (no normalization -- `terms`
/// normalizes the result afterwards). Symbols are independent variables:
/// `d(other symbol)/dx = 0`.
pub(crate) fn derivative<F: Field>(
    expr: ElementaryExpr<F>,
    wrt: &Symbol<F::Domain>,
) -> ElementaryExpr<F> {
    use ElementaryExpr::*;

    match expr {
        Const(_) => Const(F::ZERO),
        Symbol(s) => Const(if s == *wrt { F::ONE } else { F::ZERO }),
        Neg(u) => Neg(Box::new(derivative(*u, wrt))),
        Add(v) => Add(v.into_iter().map(|u| derivative(u, wrt)).collect()),
        // Leibniz: d(a_1 * ... * a_n) = sum_i a_1 * ... * (d a_i) * ... * a_n.
        // Every summand is its own product, so the factor list is cloned
        // once per summand; that is the size of the output.
        Mul(v) => Add((0..v.len())
            .map(|i| {
                let mut factors = v.clone();
                factors[i] = derivative(v[i].clone(), wrt);
                Mul(factors)
            })
            .collect()),
        Pow { base, exponent } => {
            let d_base = derivative(*base.clone(), wrt);
            let coeff = if exponent < 0 {
                F::negate(F::from_usize(exponent.unsigned_abs()))
            } else {
                F::from_usize(exponent.unsigned_abs())
            };
            Mul(vec![
                Const(coeff),
                Pow {
                    base,
                    exponent: exponent - 1,
                },
                d_base,
            ])
        }
        Fn(Elementary::Exp, u) => {
            let du = derivative(*u.clone(), wrt);
            Mul(vec![Fn(Elementary::Exp, u), du])
        }
        Fn(Elementary::Log, u) => {
            let du = derivative(*u.clone(), wrt);
            Mul(vec![
                Pow {
                    base: u,
                    exponent: -1,
                },
                du,
            ])
        }
        Fn(Elementary::Sin, u) => {
            let du = derivative(*u.clone(), wrt);
            Mul(vec![Fn(Elementary::Cos, u), du])
        }
        Fn(Elementary::Cos, u) => {
            let du = derivative(*u.clone(), wrt);
            Mul(vec![Neg(Box::new(Fn(Elementary::Sin, u))), du])
        }
        D { wrt: wrt2, inner } => derivative(derivative(*inner, &wrt2), wrt),
    }
}

/// Sorts each term's factors by [`cmp_atom`] and merges adjacent factors
/// whose atoms are `==` (not merely `cmp_atom`-equal -- see [`cmp_atom`]),
/// dropping exponent zero. Then sorts terms by [`cmp_term`] and merges
/// adjacent terms whose factor lists are `==`, dropping coefficient zero.
fn canonical<F: Field>(ts: Vec<Term<F>>) -> Vec<Term<F>> {
    let mut ts: Vec<Term<F>> = ts
        .into_iter()
        .map(|mut t| {
            t.factors.sort_by(|(a, _), (b, _)| cmp_atom(a, b));
            let mut merged: Vec<(Atom<F>, isize)> = Vec::new();
            for (atom, exp) in t.factors {
                match merged.last_mut() {
                    Some((last_atom, last_exp)) if *last_atom == atom => *last_exp += exp,
                    _ => merged.push((atom, exp)),
                }
            }
            merged.retain(|(_, e)| *e != 0);
            t.factors = merged;
            t
        })
        .collect();

    ts.sort_by(cmp_term);
    let mut out: Vec<Term<F>> = Vec::new();
    for t in ts {
        match out.last_mut() {
            Some(last) if last.factors == t.factors => {
                last.coeff = F::add(last.coeff.clone(), t.coeff);
            }
            _ => out.push(t),
        }
    }
    out.retain(|t| t.coeff != F::ZERO);
    out
}

/// Rebuilds an expression from a canonical term list. Never produces `Neg`
/// or `D`: a negated term shows up as a negative constant coefficient.
fn build_sum<F: Field>(mut ts: Vec<Term<F>>) -> ElementaryExpr<F> {
    match ts.len() {
        0 => ElementaryExpr::Const(F::ZERO),
        1 => ts.pop().unwrap().into_expr(),
        _ => ElementaryExpr::Add(ts.into_iter().map(Term::into_expr).collect()),
    }
}

/// Normalizes in place: expands to a term list and rebuilds the canonical
/// sum-of-products form.
fn normalize<F: Field>(expr: &mut ElementaryExpr<F>) {
    let taken = std::mem::replace(expr, ElementaryExpr::Add(Vec::new()));
    *expr = build_sum(canonical(terms(taken)));
}

// ================================================================================
// Formatter
// ================================================================================

/// Canonicalizes [`ElementaryExpr`]s: linearity, integer powers (including
/// negative, i.e. division), elementary-function folding, and symbolic
/// differentiation (`D` never survives). The canonical form is a sum of
/// terms `coeff · Π atomᵢ^eᵢ`, factors and terms sorted structurally with
/// like ones collected.
#[derive_where::derive_where(Default)]
pub struct ElementaryRewriter<F: Field> {
    _marker: std::marker::PhantomData<F>,
}

impl<F: Field> ElementaryRewriter<F> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<F: Field> Rewriter for ElementaryRewriter<F> {
    type Expr = ElementaryExpr<F>;

    fn rewrite_expr(&self, expr: &mut Self::Expr) {
        normalize(expr);
    }
}

#[cfg(test)]
mod tests {
    use eqn_algebra::field::{Rational, RationalField, Rationals};

    use super::*;

    type Expr = ElementaryExpr<RationalField>;

    fn c(i: i64) -> Expr {
        Expr::Const(Rational::from(i))
    }

    fn xs() -> Symbol<Rationals> {
        Symbol::new("x")
    }

    fn ys() -> Symbol<Rationals> {
        Symbol::new("y")
    }

    fn x() -> Expr {
        Expr::Symbol(xs())
    }

    fn y() -> Expr {
        Expr::Symbol(ys())
    }

    fn pow(base: Expr, exponent: isize) -> Expr {
        Expr::Pow {
            base: Box::new(base),
            exponent,
        }
    }

    fn fnc(kind: Elementary, arg: Expr) -> Expr {
        Expr::elementary(kind, arg)
    }

    fn d(wrt: Symbol<Rationals>, inner: Expr) -> Expr {
        Expr::d(wrt, inner)
    }

    fn fmt(expr: Expr) -> Expr {
        ElementaryRewriter::new().rewrited_expr(expr)
    }

    #[test]
    fn integer_powers() {
        assert_eq!(fmt(Expr::Mul(vec![x(), pow(x(), -1)])), c(1));
        assert_eq!(fmt(pow(x(), 0)), c(1));
        assert_eq!(fmt(Expr::Mul(vec![pow(x(), 3), pow(x(), -1)])), pow(x(), 2));
    }

    #[test]
    fn expands_and_collects_a_square() {
        // (x+1)^2 -> 1 + 2x + x^2. Constant term sorts first (0 factors),
        // then coeff*x (1 factor, exponent 1), then x^2 (1 factor,
        // exponent 2) -- canonical order is by factor list, shortest/lowest
        // exponent first.
        let expr = pow(Expr::Add(vec![x(), c(1)]), 2);
        assert_eq!(
            fmt(expr),
            Expr::Add(vec![c(1), Expr::Mul(vec![c(2), x()]), pow(x(), 2)])
        );
    }

    #[test]
    fn distinct_sums_with_equal_structure_do_not_merge() {
        // (x+1)^-1 * (x+2)^-1: both factors are `Sum`s that compare Equal
        // under cmp_structural (constants always tie), but they are not
        // Eq, so they must survive as two separate factors, not collapse
        // into one or cancel.
        let expr = Expr::Mul(vec![
            pow(Expr::Add(vec![x(), c(1)]), -1),
            pow(Expr::Add(vec![x(), c(2)]), -1),
        ]);
        assert_eq!(
            fmt(expr),
            Expr::Mul(vec![
                pow(Expr::Add(vec![c(1), x()]), -1),
                pow(Expr::Add(vec![c(2), x()]), -1),
            ])
        );
    }

    #[test]
    fn elementary_function_folding() {
        assert_eq!(fmt(fnc(Elementary::Exp, fnc(Elementary::Log, x()))), x());
        assert_eq!(fmt(fnc(Elementary::Exp, c(0))), c(1));
        assert_eq!(fmt(fnc(Elementary::Log, c(1))), c(0));
        assert_eq!(fmt(fnc(Elementary::Cos, c(0))), c(1));
    }

    #[test]
    fn derivatives() {
        assert_eq!(fmt(d(xs(), pow(x(), 2))), Expr::Mul(vec![c(2), x()]));
        assert_eq!(
            fmt(d(xs(), fnc(Elementary::Sin, x()))),
            fnc(Elementary::Cos, x())
        );
        assert_eq!(fmt(d(xs(), Expr::Mul(vec![x(), y()]))), y());
        assert_eq!(fmt(d(ys(), Expr::Mul(vec![x(), y()]))), x());
        assert_eq!(fmt(d(xs(), fnc(Elementary::Log, x()))), pow(x(), -1));
        assert_eq!(
            fmt(d(xs(), fnc(Elementary::Exp, Expr::Mul(vec![c(2), x()])))),
            Expr::Mul(vec![c(2), fnc(Elementary::Exp, Expr::Mul(vec![c(2), x()]))])
        );
        assert_eq!(
            fmt(d(xs(), pow(fnc(Elementary::Sin, x()), 2))),
            Expr::Mul(vec![
                c(2),
                fnc(Elementary::Sin, x()),
                fnc(Elementary::Cos, x())
            ])
        );
        assert_eq!(
            fmt(d(xs(), d(xs(), pow(x(), 3)))),
            Expr::Mul(vec![c(6), x()])
        );
        assert_eq!(fmt(d(xs(), c(5))), c(0));
    }

    #[test]
    fn derive_agrees_with_the_d_route() {
        use eqn_algebra::ring::DifferentialRing;

        type Ring = crate::ElementaryFunctionRing<RationalField>;

        assert_eq!(fmt(Ring::derive(x(), &xs())), c(1));
        assert_eq!(
            fmt(Ring::derive(fnc(Elementary::Sin, x()), &xs())),
            fmt(d(xs(), fnc(Elementary::Sin, x())))
        );
    }

    fn assert_idempotent<R: Rewriter>(rewriter: &R, expr: R::Expr)
    where
        R::Expr: PartialEq + std::fmt::Debug + Clone,
    {
        let once = rewriter.rewrited_expr(expr);
        assert_eq!(rewriter.rewrited_expr(once.clone()), once);
    }

    #[test]
    fn normalize_is_idempotent() {
        let f = ElementaryRewriter::new();
        let inputs = [
            Expr::Mul(vec![x(), pow(x(), -1)]),
            pow(x(), 0),
            Expr::Mul(vec![pow(x(), 3), pow(x(), -1)]),
            pow(Expr::Add(vec![x(), c(1)]), 2),
            Expr::Mul(vec![
                pow(Expr::Add(vec![x(), c(1)]), -1),
                pow(Expr::Add(vec![x(), c(2)]), -1),
            ]),
            fnc(Elementary::Exp, fnc(Elementary::Log, x())),
            fnc(Elementary::Exp, c(0)),
            fnc(Elementary::Log, c(1)),
            fnc(Elementary::Cos, c(0)),
            d(xs(), pow(x(), 2)),
            d(xs(), fnc(Elementary::Sin, x())),
            d(xs(), Expr::Mul(vec![x(), y()])),
            d(xs(), fnc(Elementary::Log, x())),
            d(xs(), fnc(Elementary::Exp, Expr::Mul(vec![c(2), x()]))),
            d(xs(), pow(fnc(Elementary::Sin, x()), 2)),
            d(xs(), d(xs(), pow(x(), 3))),
            d(xs(), c(5)),
        ];
        for expr in inputs {
            assert_idempotent(&f, expr);
        }
    }

    #[test]
    #[should_panic(expected = "division by zero")]
    fn inverting_zero_panics() {
        fmt(pow(c(0), -1));
    }

    #[test]
    fn inverting_an_inverse_sum_expands() {
        // ((x+1)^-1)^-2 -- inverting an already-inverted sum flips its
        // exponent back positive, which must expand rather than survive as
        // a Sum atom with a positive exponent.
        let expr = pow(pow(Expr::Add(vec![x(), c(1)]), -1), -2);
        let expected = fmt(pow(Expr::Add(vec![x(), c(1)]), 2));
        let actual = fmt(expr.clone());
        assert_eq!(actual, expected);
        assert_idempotent(&ElementaryRewriter::new(), expr);
    }
}
