use eqn_algebra::ring::{DifferentialRing, Ring, SemiRing};
use eqn_core::rewriter::Rewriter;

use crate::{Chart, DifferentialForm, Manifold, ZeroForm};

// ================================================================================
// Normalization engine
// ================================================================================

/// `coeff · dx_{i_1} ∧ ... ∧ dx_{i_n}`
#[derive_where::derive_where(Clone)]
struct Term<M: Manifold> {
    coeff: ZeroForm<M>,
    atoms: Vec<usize>,
}

impl<M: Manifold> Term<M> {
    fn one() -> Self {
        Self {
            coeff: M::Functions::ONE,
            atoms: vec![],
        }
    }

    fn negated(mut self) -> Self {
        self.coeff = M::Functions::negate(self.coeff);
        self
    }

    fn wedge(&self, other: &Self) -> Self {
        Self {
            coeff: M::Functions::multiply(self.coeff.clone(), other.coeff.clone()),
            atoms: self.atoms.iter().chain(&other.atoms).copied().collect(),
        }
    }

    fn differential(self, chart: &Chart<M>) -> Vec<Self> {
        (0..M::DIM)
            .map(|i| Self {
                coeff: M::Functions::derive(self.coeff.clone(), &chart.coordinates()[i]),
                atoms: std::iter::once(i)
                    .chain(self.atoms.iter().copied())
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

    /// The coefficient is dropped when it *is* the constant `ONE` and there
    /// is at least one wedge factor to carry the term.
    fn into_form(self, chart: &Chart<M>) -> DifferentialForm<M> {
        let mut factors: Vec<DifferentialForm<M>> = self
            .atoms
            .into_iter()
            .map(|i| {
                DifferentialForm::Differential(Box::new(DifferentialForm::Scalar(
                    chart.coordinates()[i].clone().into(),
                )))
            })
            .collect();
        let coeff_is_one = self.coeff == M::Functions::ONE;
        if factors.is_empty() || !coeff_is_one {
            factors.insert(0, DifferentialForm::Scalar(self.coeff));
        }
        match factors.len() {
            1 => factors.pop().unwrap(),
            _ => DifferentialForm::Wedged(factors),
        }
    }
}

fn terms<M: Manifold>(expr: DifferentialForm<M>, chart: &Chart<M>) -> Vec<Term<M>> {
    match expr {
        DifferentialForm::Scalar(e) => vec![Term {
            coeff: e,
            atoms: vec![],
        }],
        DifferentialForm::Neg(x) => terms(*x, chart).into_iter().map(Term::negated).collect(),
        DifferentialForm::Add(xs) => xs.into_iter().flat_map(|x| terms(x, chart)).collect(),
        DifferentialForm::Wedged(xs) => xs.into_iter().fold(vec![Term::one()], |acc, x| {
            let rhs = terms(x, chart);
            acc.iter()
                .flat_map(|a| rhs.iter().map(move |b| a.wedge(b)))
                .collect()
        }),
        DifferentialForm::Differential(x) => terms(*x, chart)
            .into_iter()
            .flat_map(|t| t.differential(chart))
            .collect(),
    }
}

/// Expands the tree into its term list by linearity, distributing `∧` over
/// `+` and real differentiation of each coefficient in the given chart;
/// terms of degree above `M::DIM` vanish. The canonical form is a flat term
/// list, so the tree is consumed rather than edited in place.
fn terms_of<M: Manifold>(expr: &mut DifferentialForm<M>, chart: &Chart<M>) -> Vec<Term<M>> {
    let taken = std::mem::replace(expr, DifferentialForm::Add(Vec::new()));
    terms(taken, chart)
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
                last.coeff = M::Functions::add(last.coeff.clone(), t.coeff);
            }
            _ => merged.push(t),
        }
    }
    merged
}

/// Rebuilds a form from its terms: normalizes each coefficient into the
/// algebra's canonical form (this is where `d² = 0` / `dc = 0` fall out, as
/// `derive` already produced a real zero for them), then drops terms whose
/// coefficient normalizes to zero.
fn build_sum<M: Manifold, N: Rewriter<Expr = ZeroForm<M>>>(
    mut ts: Vec<Term<M>>,
    chart: &Chart<M>,
    functions: &N,
) -> DifferentialForm<M> {
    for t in &mut ts {
        functions.rewrite_expr(&mut t.coeff);
    }
    ts.retain(|t| t.coeff != M::Functions::ZERO);
    match ts.len() {
        0 => DifferentialForm::Scalar(M::Functions::ZERO),
        1 => ts.pop().unwrap().into_form(chart),
        _ => DifferentialForm::Add(ts.into_iter().map(|t| t.into_form(chart)).collect()),
    }
}

/// Normalizes by the exterior-algebra laws that need no ordering; wedge
/// factors keep their written order.
fn normalize<M: Manifold, N: Rewriter<Expr = ZeroForm<M>>>(
    expr: &mut DifferentialForm<M>,
    chart: &Chart<M>,
    functions: &N,
) {
    *expr = build_sum(terms_of(expr, chart), chart, functions);
}

/// [`normalize`] plus graded commutativity: wedge factors sort into a
/// canonical order and like terms collect.
fn normalize_graded<M: Manifold, N: Rewriter<Expr = ZeroForm<M>>>(
    expr: &mut DifferentialForm<M>,
    chart: &Chart<M>,
    functions: &N,
) {
    *expr = build_sum(canonicalize(terms_of(expr, chart)), chart, functions);
}

// ================================================================================
// Formatters
// ================================================================================

/// Normalizes by the exterior-algebra laws that need no ordering: linearity,
/// `∧` distributing over `+`, Leibniz via real differentiation of
/// coefficients (`d² = 0` and `dc = 0` come from the algebra's `derive`),
/// and vanishing above degree `M::DIM` -- the exterior derivative in
/// `chart`, with 0-forms canonicalized by `functions`. Wedge factors keep
/// their written order.
pub struct ExteriorRewriter<M: Manifold, N: Rewriter<Expr = ZeroForm<M>>> {
    chart: Chart<M>,
    functions: N,
}

impl<M: Manifold, N: Rewriter<Expr = ZeroForm<M>>> ExteriorRewriter<M, N> {
    pub fn new(chart: Chart<M>, functions: N) -> Self {
        Self { chart, functions }
    }
}

impl<M: Manifold, N: Rewriter<Expr = ZeroForm<M>>> Rewriter for ExteriorRewriter<M, N> {
    type Expr = DifferentialForm<M>;

    fn rewrite_expr(&self, expr: &mut Self::Expr) {
        normalize(expr, &self.chart, &self.functions);
    }
}

/// [`ExteriorRewriter`] plus graded commutativity: wedge factors sort into
/// a canonical order with the permutation sign, `dx ∧ dx = 0`, and like
/// terms collect into one coefficient -- the exterior derivative in
/// `chart`, with 0-forms canonicalized by `functions`.
pub struct GradedCommutativeRewriter<M: Manifold, N: Rewriter<Expr = ZeroForm<M>>> {
    chart: Chart<M>,
    functions: N,
}

impl<M: Manifold, N: Rewriter<Expr = ZeroForm<M>>> GradedCommutativeRewriter<M, N> {
    pub fn new(chart: Chart<M>, functions: N) -> Self {
        Self { chart, functions }
    }
}

impl<M: Manifold, N: Rewriter<Expr = ZeroForm<M>>> Rewriter for GradedCommutativeRewriter<M, N> {
    type Expr = DifferentialForm<M>;

    fn rewrite_expr(&self, expr: &mut Self::Expr) {
        normalize_graded(expr, &self.chart, &self.functions);
    }
}

#[cfg(test)]
mod tests {
    use eqn_algebra::ring::CommutativeRingRewriter;
    use eqn_analysis::ElementaryRewriter;
    use eqn_core::symbol::Symbol;

    use super::*;
    use crate::Chart;
    use crate::tests::*;

    type Form = DifferentialForm<Plane>;
    type IntForm = DifferentialForm<IntPlane>;

    fn xy() -> Chart<Plane> {
        Chart::new([Symbol::new("x"), Symbol::new("y")])
    }

    /// A chart where `y` is not a coordinate, unlike [`xy`].
    fn xz() -> Chart<Plane> {
        Chart::new([Symbol::new("x"), Symbol::new("z")])
    }

    fn exterior(src: &str) -> Form {
        ExteriorRewriter::new(xy(), ElementaryRewriter::new()).rewrited_expr(form(src))
    }

    fn graded(src: &str) -> Form {
        GradedCommutativeRewriter::new(xy(), ElementaryRewriter::new()).rewrited_expr(form(src))
    }

    // --------------------------------------------------------------------------
    // IntPlane: the algebraic de Rham complex, `RingExpr<(Z, ZAdd, ZMul)>`
    // 0-forms
    // --------------------------------------------------------------------------

    fn ixy() -> Chart<IntPlane> {
        Chart::new([Symbol::new("x"), Symbol::new("y")])
    }

    fn int_graded(src: &str) -> IntForm {
        GradedCommutativeRewriter::new(ixy(), CommutativeRingRewriter::new())
            .rewrited_expr(int_form(src))
    }

    #[test]
    fn d_of_x_squared_y_over_int_plane() {
        // d(x^2 · y) = 2xy dx + x^2 dy
        assert_eq!(int_graded("d(x^2 y)"), int_form("2 x y dx + x^2 dy"));
    }

    #[test]
    fn d_squared_vanishes_over_int_plane() {
        assert_eq!(int_graded("d(d(x^2 y))"), int_form("0"));
    }

    #[test]
    fn d_of_wedged_product_over_int_plane() {
        // d(x·y ∧ dx) = -x dx∧dy
        assert_eq!(int_graded("d(x y ∧ dx)"), int_form("-1 x dx ∧ dy"));
    }

    #[test]
    fn d_squared_and_d_const_vanish() {
        assert_eq!(exterior("d(dx)"), form("0"));
        assert_eq!(exterior("d(7)"), form("0"));
    }

    #[test]
    fn leibniz_differentiates_a_product() {
        assert_eq!(exterior("d(x y)"), form("y dx + x dy"));
    }

    #[test]
    fn exterior_keeps_order_and_distributes() {
        assert_eq!(exterior("dy ∧ dx"), form("dy ∧ dx"));
        assert_eq!(exterior("2 ∧ (x + dy) ∧ dx"), form("2 x dx + 2 dy ∧ dx"));
    }

    #[test]
    fn graded_commutative_sorts_with_sign() {
        assert_eq!(graded("dy ∧ dx"), form("-1 dx ∧ dy"));
        assert_eq!(graded("dx ∧ dx"), form("0"));
        assert_eq!(graded("dx ∧ dy + dy ∧ dx"), form("0"));
        assert_eq!(graded("dx ∧ dy + dx ∧ dy"), form("2 dx ∧ dy"));
    }

    #[test]
    fn forms_above_dim_vanish() {
        assert_eq!(exterior("dx ∧ dy ∧ dz"), form("0"));
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
        let sources = [
            "0",
            "-(-x)",
            "-(x dy)",
            "d(x dy)",
            "dy ∧ dx",
            "dx ∧ dy + dy ∧ dx",
            "2 ∧ (x + dy) ∧ dx",
            "dx ∧ dy ∧ dx",
            "d(x^2)",
            "d(d(x^2 y))",
        ];

        let inputs = sources
            .iter()
            .map(|src| form(src))
            .chain([DifferentialForm::Add(vec![])]);
        for expr in inputs {
            assert_idempotent(
                &ExteriorRewriter::new(xy(), ElementaryRewriter::new()),
                expr.clone(),
            );
            assert_idempotent(
                &GradedCommutativeRewriter::new(xy(), ElementaryRewriter::new()),
                expr,
            );
        }

        let int_inputs = sources
            .iter()
            .map(|src| int_form(src))
            .chain([DifferentialForm::Add(vec![])]);
        for expr in int_inputs {
            assert_idempotent(
                &ExteriorRewriter::new(ixy(), CommutativeRingRewriter::new()),
                expr.clone(),
            );
            assert_idempotent(
                &GradedCommutativeRewriter::new(ixy(), CommutativeRingRewriter::new()),
                expr,
            );
        }
    }

    // --------------------------------------------------------------------------
    // `d` differentiates in coordinates
    // --------------------------------------------------------------------------

    #[test]
    fn d_of_a_square() {
        assert_eq!(graded("d(x^2)"), form("2 x dx"));
    }

    #[test]
    fn d_of_a_square_plus_sin() {
        assert_eq!(graded("d(x^2 + sin(y))"), form("2 x dx + cos(y) dy"));
    }

    #[test]
    fn d_of_a_product() {
        assert_eq!(graded("d(x y)"), form("y dx + x dy"));
    }

    #[test]
    fn d_of_wedged_product_form() {
        assert_eq!(graded("d(x y ∧ dx)"), form("-1 x dx ∧ dy"));
    }

    #[test]
    fn d_squared_via_real_differentiation() {
        assert_eq!(graded("d(d(x^2 y))"), form("0"));
    }

    #[test]
    fn repeated_atom_and_degree_above_dim_vanish() {
        assert_eq!(graded("dx ∧ dy ∧ dx"), form("0"));
        assert_eq!(graded("dx ∧ dy ∧ dz"), form("0"));
    }

    #[test]
    fn parameters_are_constant_under_d() {
        // `a` is never a chart coordinate here: a parameter. It sorts before
        // `x` in ElementaryRewriter's structural order (symbols compare by
        // name), so the coefficient is `2 a x`, not `2 x a`.
        assert_eq!(graded("d(a x^2)"), form("2 a x dx"));
        assert_eq!(graded("da"), form("0"));
    }

    #[test]
    fn d_only_sees_chart_coordinates() {
        // d(x^2 + y^2) = 2x dx + 2y dy in the (x, y) chart...
        assert_eq!(graded("d(x^2 + y^2)"), form("2 x dx + 2 y dy"));

        // ...but only 2x dx in the (x, z) chart: `y` is a parameter there,
        // so its whole term drops.
        let xz_chart = GradedCommutativeRewriter::new(xz(), ElementaryRewriter::new());
        assert_eq!(xz_chart.rewrited_expr(form("d(x^2 + y^2)")), form("2 x dx"));
    }

    #[test]
    fn chart_order_governs_canonical_order_and_sign() {
        // chart (y, x): position 0 is y, position 1 is x. Canonical order
        // follows chart position, not name, unlike the (x, y) chart used
        // everywhere else in this file, where the two coincide.
        let yx = Chart::<Plane>::new([Symbol::new("y"), Symbol::new("x")]);
        let f = GradedCommutativeRewriter::new(yx, ElementaryRewriter::new());

        // d(x*y) = x dy + y dx
        assert_eq!(f.rewrited_expr(form("d(x y)")), form("x dy + y dx"));

        // dx ∧ dy = -(dy ∧ dx): position 1 sorts after position 0.
        assert_eq!(f.rewrited_expr(form("dx ∧ dy")), form("-1 dy ∧ dx"));
    }
}
