use std::collections::BTreeSet;

use eqn_algebra::ring::SemiRing;
use eqn_analysis::{ElementaryExpr, ElementaryRewriter};
use eqn_core::rewriter::{Expression, Rewriter};

use crate::{Coordinate, DifferentialForm, Manifold, ZeroForm};

// ================================================================================
// Normalization engine
// ================================================================================

/// `coeff · dx_1 ∧ ... ∧ dx_n`; the coefficient is a 0-form.
#[derive_where::derive_where(Clone)]
struct Term<M: Manifold> {
    coeff: ZeroForm<M>,
    atoms: Vec<Coordinate<M>>,
}

impl<M: Manifold> Term<M> {
    fn one() -> Self {
        Self {
            coeff: ElementaryExpr::Const(<M::Scalar as SemiRing>::ONE),
            atoms: vec![],
        }
    }

    fn negated(mut self) -> Self {
        self.coeff = ElementaryExpr::Neg(Box::new(self.coeff));
        self
    }

    fn wedge(&self, other: &Self) -> Self {
        Self {
            coeff: ElementaryExpr::Mul(vec![self.coeff.clone(), other.coeff.clone()]),
            atoms: self.atoms.iter().chain(&other.atoms).cloned().collect(),
        }
    }

    /// `d(c · dx_I) = Σ_{s ∈ free symbols of c} (∂c/∂s) ds ∧ dx_I`. No sign:
    /// `dc` is placed in front. `d(dx) = 0` is automatic: atoms carry no
    /// coefficient of their own to differentiate.
    fn differential(self) -> Vec<Self> {
        let free: BTreeSet<Coordinate<M>> = std::iter::once(&self.coeff)
            .chain(self.coeff.descendants())
            .filter_map(Expression::as_symbol)
            .cloned()
            .collect();
        free.into_iter()
            .map(|s| Self {
                coeff: ElementaryExpr::d(s.clone(), self.coeff.clone()),
                atoms: std::iter::once(s)
                    .chain(self.atoms.iter().cloned())
                    .collect(),
            })
            .collect()
    }

    /// Sorts `atoms` with the permutation parity, dropping the term if two
    /// atoms are equal (`dx ∧ dx = 0`).
    fn canonical(mut self) -> Option<Self> {
        let mut odd = false;
        for i in 1..self.atoms.len() {
            let mut j = i;
            while j > 0 && self.atoms[j - 1] > self.atoms[j] {
                self.atoms.swap(j - 1, j);
                odd = !odd;
                j -= 1;
            }
        }
        if self.atoms.windows(2).any(|w| w[0] == w[1]) {
            return None;
        }
        Some(if odd { self.negated() } else { self })
    }

    fn into_form(self) -> DifferentialForm<M> {
        let mut factors: Vec<DifferentialForm<M>> = self
            .atoms
            .into_iter()
            .map(|s| {
                DifferentialForm::Differential(Box::new(DifferentialForm::Scalar(
                    ElementaryExpr::Symbol(s),
                )))
            })
            .collect();
        let coeff_is_one = matches!(&self.coeff, ElementaryExpr::Const(c) if c.clone() == <M::Scalar as SemiRing>::ONE);
        if factors.is_empty() || !coeff_is_one {
            factors.insert(0, DifferentialForm::Scalar(self.coeff));
        }
        match factors.len() {
            1 => factors.pop().unwrap(),
            _ => DifferentialForm::Wedged(factors),
        }
    }
}

fn terms<M: Manifold>(expr: DifferentialForm<M>) -> Vec<Term<M>> {
    match expr {
        DifferentialForm::Scalar(e) => vec![Term {
            coeff: e,
            atoms: vec![],
        }],
        DifferentialForm::Neg(x) => terms(*x).into_iter().map(Term::negated).collect(),
        DifferentialForm::Add(xs) => xs.into_iter().flat_map(terms).collect(),
        DifferentialForm::Wedged(xs) => xs.into_iter().fold(vec![Term::one()], |acc, x| {
            let rhs = terms(x);
            acc.iter()
                .flat_map(|a| rhs.iter().map(move |b| a.wedge(b)))
                .collect()
        }),
        DifferentialForm::Differential(x) => {
            terms(*x).into_iter().flat_map(Term::differential).collect()
        }
    }
}

/// Expands the tree into its term list by linearity, distributing `∧` over
/// `+` and real differentiation of each coefficient; terms of degree above
/// `M::DIM` vanish. The canonical form is a flat term list, so the tree is
/// consumed rather than edited in place.
fn terms_of<M: Manifold>(expr: &mut DifferentialForm<M>) -> Vec<Term<M>> {
    let taken = std::mem::replace(expr, DifferentialForm::Add(Vec::new()));
    terms(taken)
        .into_iter()
        .filter(|t| t.atoms.len() <= M::DIM)
        .collect()
}

/// Graded commutativity: sorts each term's wedge factors with the
/// permutation sign (`dx ∧ dx = 0` drops the term), then sorts terms by
/// their atoms and merges equal ones into a single coefficient.
fn canonicalize<M: Manifold>(ts: Vec<Term<M>>) -> Vec<Term<M>> {
    let mut ts: Vec<Term<M>> = ts.into_iter().filter_map(Term::canonical).collect();
    ts.sort_by(|a, b| a.atoms.cmp(&b.atoms));
    let mut merged: Vec<Term<M>> = vec![];
    for t in ts {
        match merged.last_mut() {
            Some(last) if last.atoms == t.atoms => {
                last.coeff = ElementaryExpr::Add(vec![last.coeff.clone(), t.coeff]);
            }
            _ => merged.push(t),
        }
    }
    merged
}

/// Rebuilds a form from its terms: normalizes each coefficient (this is
/// where `D` nodes actually differentiate, and where `d² = 0` / `dc = 0`
/// fall out as real derivatives evaluating to zero), then drops terms whose
/// coefficient normalizes to zero.
fn build_sum<M: Manifold>(mut ts: Vec<Term<M>>) -> DifferentialForm<M> {
    let elementary = ElementaryRewriter::<M::Scalar>::new();
    for t in &mut ts {
        elementary.rewrite_expr(&mut t.coeff);
    }
    ts.retain(|t| {
        !matches!(&t.coeff, ElementaryExpr::Const(c) if c.clone() == <M::Scalar as SemiRing>::ZERO)
    });
    match ts.len() {
        0 => DifferentialForm::Scalar(ElementaryExpr::Const(<M::Scalar as SemiRing>::ZERO)),
        1 => ts.pop().unwrap().into_form(),
        _ => DifferentialForm::Add(ts.into_iter().map(Term::into_form).collect()),
    }
}

/// Normalizes by the exterior-algebra laws that need no ordering; wedge
/// factors keep their written order.
fn normalize<M: Manifold>(expr: &mut DifferentialForm<M>) {
    *expr = build_sum(terms_of(expr));
}

/// [`normalize`] plus graded commutativity: wedge factors sort into a
/// canonical order and like terms collect.
fn normalize_graded<M: Manifold>(expr: &mut DifferentialForm<M>) {
    *expr = build_sum(canonicalize(terms_of(expr)));
}

// ================================================================================
// Formatters
// ================================================================================

/// Normalizes by the exterior-algebra laws that need no ordering: linearity,
/// `∧` distributing over `+`, Leibniz via real differentiation of
/// coefficients (`d² = 0` and `dc = 0` follow from that), and vanishing
/// above degree `M::DIM`. Wedge factors keep their written order.
#[derive_where::derive_where(Default)]
pub struct ExteriorRewriter<M: Manifold> {
    _marker: std::marker::PhantomData<M>,
}

impl<M: Manifold> ExteriorRewriter<M> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<M: Manifold> Rewriter for ExteriorRewriter<M> {
    type Expr = DifferentialForm<M>;

    fn rewrite_expr(&self, expr: &mut Self::Expr) {
        normalize(expr);
    }
}

/// [`ExteriorRewriter`] plus graded commutativity: wedge factors sort into
/// a canonical order with the permutation sign, `dx ∧ dx = 0`, and like
/// terms collect into one coefficient.
#[derive_where::derive_where(Default)]
pub struct GradedCommutativeRewriter<M: Manifold> {
    _marker: std::marker::PhantomData<M>,
}

impl<M: Manifold> GradedCommutativeRewriter<M> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<M: Manifold> Rewriter for GradedCommutativeRewriter<M> {
    type Expr = DifferentialForm<M>;

    fn rewrite_expr(&self, expr: &mut Self::Expr) {
        normalize_graded(expr);
    }
}

#[cfg(test)]
mod tests {
    use eqn_algebra::field::Rational;
    use eqn_core::symbol::Symbol;

    use super::*;
    use crate::Chart;
    use crate::tests::*;

    fn xy() -> Chart<Plane> {
        Chart::new([Symbol::new("x"), Symbol::new("y")])
    }

    fn x() -> ZeroForm<Plane> {
        ElementaryExpr::Symbol(Symbol::new("x"))
    }

    fn y() -> ZeroForm<Plane> {
        ElementaryExpr::Symbol(Symbol::new("y"))
    }

    fn c(i: i64) -> ZeroForm<Plane> {
        ElementaryExpr::Const(Rational::from(i))
    }

    fn sc(e: ZeroForm<Plane>) -> DifferentialForm<Plane> {
        DifferentialForm::Scalar(e)
    }

    fn dx() -> DifferentialForm<Plane> {
        xy().differential(0).unwrap()
    }

    fn dy() -> DifferentialForm<Plane> {
        xy().differential(1).unwrap()
    }

    fn wedge(xs: Vec<DifferentialForm<Plane>>) -> DifferentialForm<Plane> {
        DifferentialForm::Wedged(xs)
    }

    fn d(x: DifferentialForm<Plane>) -> DifferentialForm<Plane> {
        DifferentialForm::Differential(Box::new(x))
    }

    fn pow(base: ZeroForm<Plane>, exponent: isize) -> ZeroForm<Plane> {
        ElementaryExpr::Pow {
            base: Box::new(base),
            exponent,
        }
    }

    #[test]
    fn d_squared_and_d_const_vanish() {
        let f = ExteriorRewriter::<Plane>::new();
        assert_eq!(f.rewrited_expr(d(dx())), sc(c(0)));
        assert_eq!(f.rewrited_expr(d(sc(c(7)))), sc(c(0)));
    }

    #[test]
    fn leibniz_differentiates_a_product() {
        let f = ExteriorRewriter::<Plane>::new();
        // d(x*y) = y dx + x dy
        assert_eq!(
            f.rewrited_expr(d(sc(ElementaryExpr::Mul(vec![x(), y()])))),
            DifferentialForm::Add(vec![wedge(vec![sc(y()), dx()]), wedge(vec![sc(x()), dy()])])
        );
    }

    #[test]
    fn exterior_keeps_order_and_distributes() {
        let f = ExteriorRewriter::<Plane>::new();
        assert_eq!(
            f.rewrited_expr(wedge(vec![dy(), dx()])),
            wedge(vec![dy(), dx()])
        );
        // 2 ∧ (x + dy) ∧ dx = 2x ∧ dx + 2 dy ∧ dx
        let e = wedge(vec![
            sc(c(2)),
            DifferentialForm::Add(vec![sc(x()), dy()]),
            dx(),
        ]);
        assert_eq!(
            f.rewrited_expr(e),
            DifferentialForm::Add(vec![
                wedge(vec![sc(ElementaryExpr::Mul(vec![c(2), x()])), dx()]),
                wedge(vec![sc(c(2)), dy(), dx()]),
            ])
        );
    }

    #[test]
    fn graded_commutative_sorts_with_sign() {
        let f = GradedCommutativeRewriter::<Plane>::new();
        // dy ∧ dx = -(dx ∧ dy)
        assert_eq!(
            f.rewrited_expr(wedge(vec![dy(), dx()])),
            wedge(vec![sc(c(-1)), dx(), dy()])
        );
        // dx ∧ dx = 0
        assert_eq!(f.rewrited_expr(wedge(vec![dx(), dx()])), sc(c(0)));
        // dx ∧ dy + dy ∧ dx = 0 ; dx ∧ dy + dx ∧ dy = 2 dx ∧ dy
        let a = wedge(vec![dx(), dy()]);
        let b = wedge(vec![dy(), dx()]);
        assert_eq!(
            f.rewrited_expr(DifferentialForm::Add(vec![a.clone(), b])),
            sc(c(0))
        );
        assert_eq!(
            f.rewrited_expr(DifferentialForm::Add(vec![a.clone(), a])),
            wedge(vec![sc(c(2)), dx(), dy()])
        );
    }

    #[test]
    fn forms_above_dim_vanish() {
        let dz = d(sc(ElementaryExpr::Symbol(Symbol::new("z"))));
        let top = wedge(vec![dx(), dy(), dz]);
        assert_eq!(
            ExteriorRewriter::<Plane>::new().rewrited_expr(top),
            sc(c(0))
        );
    }

    fn assert_idempotent<R: Rewriter>(rewriter: &R, expr: R::Expr)
    where
        R::Expr: PartialEq + std::fmt::Debug,
    {
        let once = rewriter.rewrited_expr(expr);
        assert_eq!(rewriter.rewrited_expr(once.clone()), once);
    }

    #[test]
    fn normalize_is_idempotent() {
        let inputs = [
            sc(c(0)),
            DifferentialForm::Add(vec![]),
            DifferentialForm::Neg(Box::new(DifferentialForm::Neg(Box::new(sc(x()))))),
            d(wedge(vec![sc(x()), dy()])),
            wedge(vec![dy(), dx()]),
            DifferentialForm::Add(vec![wedge(vec![dx(), dy()]), wedge(vec![dy(), dx()])]),
            wedge(vec![
                sc(c(2)),
                DifferentialForm::Add(vec![sc(x()), dy()]),
                dx(),
            ]),
            wedge(vec![dx(), dy(), dx()]),
            d(sc(pow(x(), 2))),
            d(d(sc(ElementaryExpr::Mul(vec![pow(x(), 2), y()])))),
        ];
        for expr in inputs {
            assert_idempotent(&ExteriorRewriter::<Plane>::new(), expr.clone());
            assert_idempotent(&GradedCommutativeRewriter::<Plane>::new(), expr);
        }
    }

    // --------------------------------------------------------------------------
    // `d` differentiates in coordinates
    // --------------------------------------------------------------------------

    #[test]
    fn d_of_a_square() {
        // d(x^2) = 2x dx
        let f = GradedCommutativeRewriter::<Plane>::new();
        assert_eq!(
            f.rewrited_expr(d(sc(pow(x(), 2)))),
            wedge(vec![sc(ElementaryExpr::Mul(vec![c(2), x()])), dx()])
        );
    }

    #[test]
    fn d_of_a_square_plus_sin() {
        // d(x^2 + sin y) = 2x dx + cos(y) dy
        let f = GradedCommutativeRewriter::<Plane>::new();
        let expr = sc(ElementaryExpr::Add(vec![
            pow(x(), 2),
            ElementaryExpr::elementary(eqn_analysis::Elementary::Sin, y()),
        ]));
        assert_eq!(
            f.rewrited_expr(d(expr)),
            DifferentialForm::Add(vec![
                wedge(vec![sc(ElementaryExpr::Mul(vec![c(2), x()])), dx()]),
                wedge(vec![
                    sc(ElementaryExpr::elementary(
                        eqn_analysis::Elementary::Cos,
                        y()
                    )),
                    dy()
                ]),
            ])
        );
    }

    #[test]
    fn d_of_a_product() {
        // d(x*y) = y dx + x dy
        let f = GradedCommutativeRewriter::<Plane>::new();
        assert_eq!(
            f.rewrited_expr(d(sc(ElementaryExpr::Mul(vec![x(), y()])))),
            DifferentialForm::Add(vec![wedge(vec![sc(y()), dx()]), wedge(vec![sc(x()), dy()])])
        );
    }

    #[test]
    fn d_of_wedged_product_form() {
        // d(xy ∧ dx) = -x dx∧dy
        let f = GradedCommutativeRewriter::<Plane>::new();
        let xy_dx = wedge(vec![sc(ElementaryExpr::Mul(vec![x(), y()])), dx()]);
        assert_eq!(
            f.rewrited_expr(d(xy_dx)),
            wedge(vec![sc(ElementaryExpr::Mul(vec![c(-1), x()])), dx(), dy()])
        );
    }

    #[test]
    fn d_squared_via_real_differentiation() {
        // d(d(x^2 y)) = 0
        let f = GradedCommutativeRewriter::<Plane>::new();
        let expr = sc(ElementaryExpr::Mul(vec![pow(x(), 2), y()]));
        assert_eq!(f.rewrited_expr(d(d(expr))), sc(c(0)));
    }

    #[test]
    fn repeated_atom_and_degree_above_dim_vanish() {
        let f = GradedCommutativeRewriter::<Plane>::new();
        assert_eq!(f.rewrited_expr(wedge(vec![dx(), dy(), dx()])), sc(c(0)));

        let dz = d(sc(ElementaryExpr::Symbol(Symbol::new("z"))));
        let top = wedge(vec![dx(), dy(), dz]);
        assert_eq!(f.rewrited_expr(top), sc(c(0)));
    }
}
