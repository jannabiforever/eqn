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

impl<F: Field> ElementaryExpr<F> {
    /// Structural order used for canonical sorting. Never compares domain
    /// elements: constants tie (at most one constant survives folding within a
    /// term, so the tie is harmless), which keeps `Ord` off the domain.
    fn cmp_structural(&self, b: &Self) -> std::cmp::Ordering {
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

        match (self, b) {
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
            ) => sb.cmp_structural(ob).then(se.cmp(oe)),
            (Fn(sk, sa), Fn(ok, oa)) => sk.cmp(ok).then_with(|| sa.cmp_structural(oa)),
            (Mul(s), Mul(o)) | (Add(s), Add(o)) => s
                .iter()
                .zip(o)
                .map(|(i, j)| i.cmp_structural(j))
                .find(|c| *c != Ordering::Equal)
                .unwrap_or(s.len().cmp(&o.len())),
            (Neg(s), Neg(o)) => s.cmp_structural(o),
            (D { wrt: sw, inner: si }, D { wrt: ow, inner: oi }) => {
                sw.cmp(ow).then_with(|| si.cmp_structural(oi))
            }
            (a, b) => rank(a).cmp(&rank(b)),
        }
    }

    /// Expands the tree into its term list: linearity, `Mul` cartesian product,
    /// integer powers, elementary-function constant folding and `exp \circ log`
    /// cancellation, and `D` via [`Self::derivative`]. The result is not yet
    /// sorted or merged; that is [`Term::canonical`]'s job.
    fn terms(self) -> Vec<Term<F>> {
        match self {
            ElementaryExpr::Const(c) => vec![Term {
                coeff: c,
                factors: vec![],
            }],
            ElementaryExpr::Symbol(s) => vec![Term {
                coeff: F::ONE,
                factors: vec![(Atom::Symbol(s), 1)],
            }],
            ElementaryExpr::Neg(x) => x.terms().into_iter().map(Term::negated).collect(),
            ElementaryExpr::Add(xs) => xs.into_iter().flat_map(Self::terms).collect(),
            ElementaryExpr::Mul(xs) => xs.into_iter().fold(vec![Term::one()], |acc, x| {
                let rhs = x.terms();
                acc.iter()
                    .flat_map(|a| rhs.iter().map(move |b| a.mul(b)))
                    .collect()
            }),
            ElementaryExpr::Pow { base, exponent } => base.pow_terms(exponent),
            ElementaryExpr::Fn(kind, arg) => arg.fn_terms(kind),
            ElementaryExpr::D { wrt, inner } => inner.derivative(&wrt).terms(),
        }
    }

    /// `self^n` as a term list. `n == 0` is one; `n > 0` is repeated
    /// multiplication; `n < 0` inverts (single-term base only -- a genuine sum
    /// stays an opaque [`Atom::Sum`] factor, since a field has no general
    /// `(a + b)^-1` law). Panics if `self` normalizes to zero, matching
    /// [`Field::invert`]'s contract on `ZERO`.
    fn pow_terms(self, n: isize) -> Vec<Term<F>> {
        let b = Term::canonical(self.terms());

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
                    term.into_expr().terms()
                } else {
                    vec![term]
                }
            }
            _ => vec![Term {
                coeff: F::ONE,
                factors: vec![(Atom::Sum(Self::from_terms(b)), n)],
            }],
        }
    }

    /// `kind(self)` as a term list: folds the four boundary values
    /// (`exp 0 = 1`, `log 1 = 0`, `sin 0 = 0`, `cos 0 = 1`) and cancels
    /// `exp \circ log` and `log \circ exp`; otherwise stays one opaque
    /// [`Atom::Fn`] factor.
    fn fn_terms(self, kind: Elementary) -> Vec<Term<F>> {
        use Elementary::{Cos, Exp, Log, Sin};

        let a = Self::from_terms(Term::canonical(self.terms()));
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
            (Exp, ElementaryExpr::Fn(Log, u)) => u.terms(),
            (Log, ElementaryExpr::Fn(Exp, u)) => u.terms(),
            (k, a) => vec![Term {
                coeff: F::ONE,
                factors: vec![(Atom::Fn(k, a), 1)],
            }],
        }
    }

    /// Symbolic differentiation on the raw tree (no normalization -- `terms`
    /// normalizes the result afterwards). Symbols are independent variables:
    /// `d(other symbol)/dx = 0`.
    pub(crate) fn derivative(self, wrt: &Symbol<F::Domain>) -> Self {
        use ElementaryExpr::*;

        match self {
            Const(_) => Const(F::ZERO),
            Symbol(s) => Const(if s == *wrt { F::ONE } else { F::ZERO }),
            Neg(u) => Neg(Box::new(u.derivative(wrt))),
            Add(v) => Add(v.into_iter().map(|u| u.derivative(wrt)).collect()),
            // Leibniz: d(a_1 * ... * a_n) = sum_i a_1 * ... * (d a_i) * ... * a_n.
            // Every summand is its own product, so the factor list is cloned
            // once per summand; that is the size of the output.
            Mul(v) => Add((0..v.len())
                .map(|i| {
                    let mut factors = v.clone();
                    factors[i] = v[i].clone().derivative(wrt);
                    Mul(factors)
                })
                .collect()),
            Pow { base, exponent } => {
                let d_base = (*base.clone()).derivative(wrt);
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
                let du = (*u.clone()).derivative(wrt);
                Mul(vec![Fn(Elementary::Exp, u), du])
            }
            Fn(Elementary::Log, u) => {
                let du = (*u.clone()).derivative(wrt);
                Mul(vec![
                    Pow {
                        base: u,
                        exponent: -1,
                    },
                    du,
                ])
            }
            Fn(Elementary::Sin, u) => {
                let du = (*u.clone()).derivative(wrt);
                Mul(vec![Fn(Elementary::Cos, u), du])
            }
            Fn(Elementary::Cos, u) => {
                let du = (*u.clone()).derivative(wrt);
                Mul(vec![Neg(Box::new(Fn(Elementary::Sin, u))), du])
            }
            D { wrt: wrt2, inner } => inner.derivative(&wrt2).derivative(wrt),
        }
    }

    /// Rebuilds an expression from a canonical term list. Never produces `Neg`
    /// or `D`: a negated term shows up as a negative constant coefficient.
    fn from_terms(mut ts: Vec<Term<F>>) -> Self {
        match ts.len() {
            0 => ElementaryExpr::Const(F::ZERO),
            1 => ts.pop().unwrap().into_expr(),
            _ => ElementaryExpr::Add(ts.into_iter().map(Term::into_expr).collect()),
        }
    }

    /// Normalizes in place: expands to a term list and rebuilds the canonical
    /// sum-of-products form.
    fn normalize(&mut self) {
        let taken = std::mem::replace(self, ElementaryExpr::Add(Vec::new()));
        *self = Self::from_terms(Term::canonical(taken.terms()));
    }
}

impl<F: Field> Atom<F> {
    /// Structural order over atoms: symbols by name, functions by kind then
    /// argument, sums structurally. Ties (e.g. two `Sum`s whose constants
    /// happen to be at the same structural position) are broken by insertion
    /// order in [`Term::canonical`]; merging uses `==`, never this comparator.
    fn cmp_structural(&self, b: &Self) -> std::cmp::Ordering {
        const fn rank<F: Field>(a: &Atom<F>) -> u8 {
            match a {
                Atom::Symbol(_) => 0,
                Atom::Fn(_, _) => 1,
                Atom::Sum(_) => 2,
            }
        }

        match (self, b) {
            (Atom::Symbol(s), Atom::Symbol(o)) => s.cmp(o),
            (Atom::Fn(sk, sa), Atom::Fn(ok, oa)) => sk.cmp(ok).then_with(|| sa.cmp_structural(oa)),
            (Atom::Sum(s), Atom::Sum(o)) => s.cmp_structural(o),
            (a, b) => rank(a).cmp(&rank(b)),
        }
    }
}

impl<F: Field> Term<F> {
    /// Lexicographic order over a term's factor list: [`Atom::cmp_structural`]
    /// on each atom, then the exponent, then length.
    fn cmp_structural(&self, b: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        self.factors
            .iter()
            .zip(&b.factors)
            .map(|((aa, ae), (ba, be))| aa.cmp_structural(ba).then(ae.cmp(be)))
            .find(|c| *c != Ordering::Equal)
            .unwrap_or(self.factors.len().cmp(&b.factors.len()))
    }

    /// Sorts each term's factors by [`Atom::cmp_structural`] and merges
    /// adjacent factors whose atoms are `==` (not merely comparator-equal --
    /// see [`Atom::cmp_structural`]), dropping exponent zero. Then sorts terms
    /// by [`Self::cmp_structural`] and merges adjacent terms whose factor lists
    /// are `==`, dropping coefficient zero.
    fn canonical(ts: Vec<Self>) -> Vec<Self> {
        let mut ts: Vec<Self> = ts
            .into_iter()
            .map(|mut t| {
                t.factors.sort_by(|(a, _), (b, _)| a.cmp_structural(b));
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

        ts.sort_by(Self::cmp_structural);
        let mut out: Vec<Self> = Vec::new();
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
}

// ================================================================================
// Formatter
// ================================================================================

/// Canonicalizes [`ElementaryExpr`]s: linearity, integer powers (including
/// negative, i.e. division), elementary-function folding, and symbolic
/// differentiation (`D` never survives). The canonical form is a sum of
/// terms `coeff \cdot \prod atom_i^e_i`, factors and terms sorted structurally
/// with like ones collected.
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
        expr.normalize();
    }
}

#[cfg(test)]
mod tests {

    use eqn_algebra::operator_impl::{QAdd, QMul};
    use eqn_core::set::{Q, Rational};

    use super::*;

    type Expr = ElementaryExpr<(Q, QAdd, QMul)>;

    fn c(i: i64) -> Expr {
        Expr::Const(Rational {
            numerator: i,
            denominator: 1,
        })
    }

    fn xs() -> Symbol<Q> {
        Symbol::new("x")
    }

    fn ys() -> Symbol<Q> {
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

    fn d(wrt: Symbol<Q>, inner: Expr) -> Expr {
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

        type Ring = crate::ElementaryFunctionRing<(Q, QAdd, QMul)>;

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
