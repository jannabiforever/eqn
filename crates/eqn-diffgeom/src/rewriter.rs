use eqn_algebra::ring::{Ring, SemiRing};
use eqn_core::rewriter::Rewriter;
use eqn_core::symbol::Symbol;

use crate::{DifferentialForm, Manifold, Scalar, ZeroForms};

// ================================================================================
// Normalization engine
// ================================================================================

/// A wedge factor after normalization: a function `f` (degree 0) or its
/// differential `df` (degree 1). Nothing else survives: `dc = 0`, `d(df) = 0`.
#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
enum Atom<S> {
    F(S),
    D(S),
}

impl<S> Atom<S> {
    fn degree(&self) -> usize {
        match self {
            Atom::F(_) => 0,
            Atom::D(_) => 1,
        }
    }
}

/// `coeff · a_1 ∧ … ∧ a_n`.
#[derive_where::derive_where(Clone)]
struct Term<M: Manifold> {
    coeff: Scalar<M>,
    atoms: Vec<Atom<Symbol<ZeroForms<M>>>>,
}

impl<M: Manifold> Term<M> {
    const fn one() -> Self {
        Self {
            coeff: <M::Scalar as SemiRing>::ONE,
            atoms: vec![],
        }
    }

    fn negated(mut self) -> Self {
        self.coeff = M::Scalar::negate(self.coeff);
        self
    }

    fn wedge(&self, other: &Self) -> Self {
        Self {
            coeff: M::Scalar::multiply(self.coeff.clone(), other.coeff.clone()),
            atoms: self.atoms.iter().chain(&other.atoms).cloned().collect(),
        }
    }

    fn degree(&self) -> usize {
        self.atoms.iter().map(Atom::degree).sum()
    }

    /// Leibniz: `d(a_1 ∧ … ∧ a_n) = Σ_i (-1)^{deg(a_1 … a_{i-1})} a_1 ∧ … ∧ d
    /// a_i ∧ … ∧ a_n`.
    fn differential(self) -> Vec<Self> {
        let mut out = vec![];
        let mut odd = false;
        for (i, a) in self.atoms.iter().enumerate() {
            if let Atom::F(f) = a {
                let mut atoms = self.atoms.clone();
                atoms[i] = Atom::D(f.clone());
                let t = Self {
                    coeff: self.coeff.clone(),
                    atoms,
                };
                out.push(if odd { t.negated() } else { t });
            }
            odd ^= a.degree() % 2 == 1;
        }
        out
    }

    fn canonical(mut self) -> Option<Self> {
        let (mut fs, mut ds): (Vec<_>, Vec<_>) = self
            .atoms
            .into_iter()
            .partition(|a| matches!(a, Atom::F(_)));
        fs.sort();
        let mut odd = false;
        for i in 1..ds.len() {
            let mut j = i;
            while j > 0 && ds[j - 1] > ds[j] {
                ds.swap(j - 1, j);
                odd = !odd;
                j -= 1;
            }
        }
        if ds.windows(2).any(|w| w[0] == w[1]) {
            return None;
        }
        fs.extend(ds);
        self.atoms = fs;
        Some(if odd { self.negated() } else { self })
    }

    fn into_form(self) -> DifferentialForm<M> {
        let mut factors: Vec<DifferentialForm<M>> = self
            .atoms
            .into_iter()
            .map(|a| match a {
                Atom::F(f) => DifferentialForm::Function(f),
                Atom::D(f) => {
                    DifferentialForm::Differential(Box::new(DifferentialForm::Function(f)))
                }
            })
            .collect();
        if factors.is_empty() || self.coeff != <M::Scalar as SemiRing>::ONE {
            factors.insert(0, DifferentialForm::Const(self.coeff));
        }
        match factors.len() {
            1 => factors.pop().unwrap(),
            _ => DifferentialForm::Wedged(factors),
        }
    }
}

fn terms<M: Manifold>(expr: DifferentialForm<M>) -> Vec<Term<M>> {
    match expr {
        DifferentialForm::Const(c) => vec![Term {
            coeff: c,
            atoms: vec![],
        }],
        DifferentialForm::Function(f) => vec![Term {
            coeff: <M::Scalar as SemiRing>::ONE,
            atoms: vec![Atom::F(f)],
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
/// `+`, Leibniz, `dc = 0` and `d² = 0`; terms of degree above `M::DIM`
/// vanish. The canonical form is a flat term list, so the tree is consumed
/// rather than edited in place.
fn terms_of<M: Manifold>(expr: &mut DifferentialForm<M>) -> Vec<Term<M>> {
    let taken = std::mem::replace(expr, DifferentialForm::Add(Vec::new()));
    terms(taken)
        .into_iter()
        .filter(|t| t.degree() <= M::DIM)
        .collect()
}

/// Graded commutativity: sorts each term's wedge factors with the permutation
/// sign (`df ∧ df = 0` drops the term), then sorts terms and merges equal
/// ones into a single coefficient.
fn canonicalize<M: Manifold>(ts: Vec<Term<M>>) -> Vec<Term<M>> {
    let mut ts: Vec<Term<M>> = ts.into_iter().filter_map(Term::canonical).collect();
    ts.sort_by(|a, b| a.atoms.cmp(&b.atoms));
    let mut merged: Vec<Term<M>> = vec![];
    for t in ts {
        match merged.last_mut() {
            Some(last) if last.atoms == t.atoms => {
                last.coeff = M::Scalar::add(last.coeff.clone(), t.coeff);
            }
            _ => merged.push(t),
        }
    }
    merged
}

/// Rebuilds a form from its terms, dropping zero coefficients.
fn build_sum<M: Manifold>(mut ts: Vec<Term<M>>) -> DifferentialForm<M> {
    ts.retain(|t| t.coeff != <M::Scalar as SemiRing>::ZERO);
    match ts.len() {
        0 => DifferentialForm::Const(<M::Scalar as SemiRing>::ZERO),
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
/// `∧` distributing over `+`, `dc = 0`, `d² = 0`, Leibniz, constant folding,
/// and vanishing above degree `M::DIM`. Wedge factors keep their written order.
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
/// a canonical order with the permutation sign, `df ∧ df = 0`, and like
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
    use super::*;
    use crate::Chart;
    use crate::tests::*;

    fn xy() -> Chart<Plane> {
        Chart::new([Symbol::new("x"), Symbol::new("y")])
    }

    fn wedge(xs: Vec<DifferentialForm<Plane>>) -> DifferentialForm<Plane> {
        DifferentialForm::Wedged(xs)
    }

    fn d(x: DifferentialForm<Plane>) -> DifferentialForm<Plane> {
        DifferentialForm::Differential(Box::new(x))
    }

    #[test]
    fn d_squared_and_d_const_vanish() {
        let f = ExteriorRewriter::<Plane>::new();
        assert_eq!(
            f.rewrited_expr(d(xy().differential(0).unwrap())),
            DifferentialForm::Const(0)
        );
        assert_eq!(
            f.rewrited_expr(d(DifferentialForm::Const(7))),
            DifferentialForm::Const(0)
        );
    }

    #[test]
    fn leibniz_picks_up_sign() {
        let c = xy();
        let (x, y, dx, dy) = (
            c.coordinate(0).unwrap(),
            c.coordinate(1).unwrap(),
            c.differential(0).unwrap(),
            c.differential(1).unwrap(),
        );
        let f = ExteriorRewriter::<Plane>::new();
        // d(x ∧ dy) = dx ∧ dy
        assert_eq!(
            f.rewrited_expr(d(wedge(vec![x, dy.clone()]))),
            wedge(vec![dx.clone(), dy.clone()])
        );
        // d(dx ∧ y) = -(dx ∧ dy), no reordering in the plain formatter
        assert_eq!(
            f.rewrited_expr(d(wedge(vec![dx.clone(), y]))),
            wedge(vec![DifferentialForm::Const(-1), dx, dy])
        );
    }

    #[test]
    fn exterior_keeps_order_and_distributes() {
        let c = xy();
        let (x, dx, dy) = (
            c.coordinate(0).unwrap(),
            c.differential(0).unwrap(),
            c.differential(1).unwrap(),
        );
        let f = ExteriorRewriter::<Plane>::new();
        assert_eq!(
            f.rewrited_expr(wedge(vec![dy.clone(), dx.clone()])),
            wedge(vec![dy.clone(), dx.clone()])
        );
        // 2 ∧ (x + dy) ∧ dx = 2 x ∧ dx + 2 dy ∧ dx
        let e = wedge(vec![
            DifferentialForm::Const(2),
            DifferentialForm::Add(vec![x.clone(), dy.clone()]),
            dx.clone(),
        ]);
        assert_eq!(
            f.rewrited_expr(e),
            DifferentialForm::Add(vec![
                wedge(vec![DifferentialForm::Const(2), x, dx.clone()]),
                wedge(vec![DifferentialForm::Const(2), dy, dx]),
            ])
        );
    }

    #[test]
    fn graded_commutative_sorts_with_sign() {
        let c = xy();
        let (dx, dy) = (c.differential(0).unwrap(), c.differential(1).unwrap());
        let f = GradedCommutativeRewriter::<Plane>::new();
        // dy ∧ dx = -(dx ∧ dy)
        assert_eq!(
            f.rewrited_expr(wedge(vec![dy.clone(), dx.clone()])),
            wedge(vec![DifferentialForm::Const(-1), dx.clone(), dy.clone()])
        );
        // dx ∧ dx = 0
        assert_eq!(
            f.rewrited_expr(wedge(vec![dx.clone(), dx.clone()])),
            DifferentialForm::Const(0)
        );
        // dx ∧ dy + dy ∧ dx = 0 ; dx ∧ dy + dx ∧ dy = 2 dx ∧ dy
        let a = wedge(vec![dx.clone(), dy.clone()]);
        let b = wedge(vec![dy.clone(), dx.clone()]);
        assert_eq!(
            f.rewrited_expr(DifferentialForm::Add(vec![a.clone(), b])),
            DifferentialForm::Const(0)
        );
        assert_eq!(
            f.rewrited_expr(DifferentialForm::Add(vec![a.clone(), a])),
            wedge(vec![DifferentialForm::Const(2), dx, dy])
        );
    }

    #[test]
    fn forms_above_dim_vanish() {
        let c = xy();
        let dz = d(DifferentialForm::Function(Symbol::new("z")));
        let top = wedge(vec![
            c.differential(0).unwrap(),
            c.differential(1).unwrap(),
            dz,
        ]);
        assert_eq!(
            ExteriorRewriter::<Plane>::new().rewrited_expr(top),
            DifferentialForm::Const(0)
        );
    }
}
