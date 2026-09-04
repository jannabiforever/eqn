// mgca: lets `Chart` carry `[_; M::DIM]` with `DIM` an associated const.
#![feature(min_generic_const_args, macroless_generic_const_args)]
#![allow(incomplete_features)]

use std::collections::HashSet;

use eqn_algebra::ring::{Ring, SemiRing};
use eqn_core::formatter::{Expression, Formatter};
use eqn_core::set::Set;
use eqn_core::symbol::Symbol;

pub const WEDGE_CHAR: char = '\u{2227}';
pub const PARTIAL_DIFFERENTIAL_CHAR: char = '\u{2202}';

/// a marker trait for smoothness.
///
/// NOTE: for now, it only support for real manifolds.
pub trait Manifold {
    type Scalar: Ring;

    type const DIM: usize;
}

/// An element of the scalar ring of `M`.
pub type Scalar<M> = <<<M as Manifold>::Scalar as SemiRing>::Domain as Set>::Element;

/// The set of 0-forms on `M`, i.e. smooth functions `M -> Scalar`.
pub struct ZeroForms<M: Manifold>(std::marker::PhantomData<M>);

impl<M: Manifold> Set for ZeroForms<M> {
    type Element = Scalar<M>;
}

#[derive_where::derive_where(Clone, Debug, PartialEq)]
pub enum DifferentialForm<M: Manifold> {
    Const(Scalar<M>),
    /// unknown `f: M -> Scalar`, a 0-form.
    Function(Symbol<ZeroForms<M>>),
    Neg(Box<Self>),
    Add(Vec<Self>),
    Wedged(Vec<Self>),
    Differential(Box<Self>),
}

impl<M: Manifold> From<Symbol<ZeroForms<M>>> for DifferentialForm<M> {
    fn from(value: Symbol<ZeroForms<M>>) -> Self {
        Self::Function(value)
    }
}

impl<M: Manifold> DifferentialForm<M> {
    fn children(&self) -> Vec<&Self> {
        match self {
            Self::Const(_) | Self::Function(_) => vec![],
            Self::Neg(inner) | Self::Differential(inner) => vec![inner],
            Self::Add(forms) | Self::Wedged(forms) => forms.iter().collect(),
        }
    }

    fn children_mut(&mut self) -> Vec<&mut Self> {
        match self {
            Self::Const(_) | Self::Function(_) => vec![],
            Self::Neg(inner) | Self::Differential(inner) => vec![inner],
            Self::Add(forms) | Self::Wedged(forms) => forms.iter_mut().collect(),
        }
    }
}

impl<M: Manifold> Expression for DifferentialForm<M> {
    type Domain = ZeroForms<M>;

    fn degrees_of_freedom(&self) -> usize {
        let mut visited = HashSet::new();
        let mut to_visit = vec![self];
        while let Some(e) = to_visit.pop() {
            if let Self::Function(f) = e {
                visited.insert(f);
            }
            to_visit.extend(e.children());
        }
        visited.len()
    }

    fn substitute(&mut self, sym: Symbol<Self::Domain>, expr: &Self) {
        let mut to_visit = vec![self];
        while let Some(e) = to_visit.pop() {
            match e {
                Self::Function(f) if *f == sym => *e = expr.clone(),
                _ => to_visit.extend(e.children_mut()),
            }
        }
    }
}

/// A coordinate chart
pub struct Chart<M: Manifold> {
    coordinates: [Symbol<ZeroForms<M>>; M::DIM],
}

impl<M: Manifold> Chart<M> {
    pub fn new(coordinates: [Symbol<ZeroForms<M>>; M::DIM]) -> Self {
        Self { coordinates }
    }

    pub fn coordinates(&self) -> &[Symbol<ZeroForms<M>>; M::DIM] {
        &self.coordinates
    }

    /// `x^i` as a 0-form.
    pub fn coordinate(&self, i: usize) -> Option<DifferentialForm<M>> {
        self.coordinates
            .get(i)
            .cloned()
            .map(DifferentialForm::Function)
    }

    /// `dx^i`.
    pub fn differential(&self, i: usize) -> Option<DifferentialForm<M>> {
        self.coordinate(i)
            .map(|c| DifferentialForm::Differential(Box::new(c)))
    }
}

// ================================================================================
// Formatters
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

/// Canonical form: a sum of terms, each a scalar times a wedge of atoms.
/// Terms of degree above `M::DIM` vanish. With `canonical`, wedge factors
/// are sorted by graded commutativity and like terms are collected.
fn normalize<M: Manifold>(expr: DifferentialForm<M>, canonical: bool) -> DifferentialForm<M> {
    let mut ts: Vec<Term<M>> = terms(expr)
        .into_iter()
        .filter(|t| t.degree() <= M::DIM)
        .collect();

    if canonical {
        ts = ts.into_iter().filter_map(Term::canonical).collect();
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
        ts = merged;
    }

    ts.retain(|t| t.coeff != <M::Scalar as SemiRing>::ZERO);
    match ts.len() {
        0 => DifferentialForm::Const(<M::Scalar as SemiRing>::ZERO),
        1 => ts.pop().unwrap().into_form(),
        _ => DifferentialForm::Add(ts.into_iter().map(Term::into_form).collect()),
    }
}

/// Normalizes by the exterior-algebra laws that need no ordering: linearity,
/// `∧` distributing over `+`, `dc = 0`, `d² = 0`, Leibniz, constant folding,
/// and vanishing above degree `M::DIM`. Wedge factors keep their written order.
#[derive_where::derive_where(Default)]
pub struct ExteriorFormatter<M: Manifold> {
    _marker: std::marker::PhantomData<M>,
}

impl<M: Manifold> ExteriorFormatter<M> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<M: Manifold> Formatter for ExteriorFormatter<M> {
    type Expr = DifferentialForm<M>;

    fn format_expr(&self, expr: Self::Expr) -> Self::Expr {
        normalize(expr, false)
    }
}

/// [`ExteriorFormatter`] plus graded commutativity: wedge factors sort into
/// a canonical order with the permutation sign, `df ∧ df = 0`, and like
/// terms collect into one coefficient.
#[derive_where::derive_where(Default)]
pub struct GradedCommutativeFormatter<M: Manifold> {
    _marker: std::marker::PhantomData<M>,
}

impl<M: Manifold> GradedCommutativeFormatter<M> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<M: Manifold> Formatter for GradedCommutativeFormatter<M> {
    type Expr = DifferentialForm<M>;

    fn format_expr(&self, expr: Self::Expr) -> Self::Expr {
        normalize(expr, true)
    }
}

#[cfg(test)]
mod tests {
    use eqn_core::op::{Associative, BinaryOperator, Commutative, Identity, Inverse};

    use super::*;

    #[derive(Set)]
    #[set(element = i64)] // ponytail: i64 stands in for R; swap for a real type when evaluation lands
    struct Reals;

    #[derive(Associative, Commutative)]
    struct Add;
    impl BinaryOperator for Add {
        type Domain = Reals;
        fn apply(a: i64, b: i64) -> i64 {
            a + b
        }
    }
    impl Identity for Add {
        const IDENTITY: i64 = 0;
    }
    impl Inverse for Add {
        fn inverse(a: i64) -> i64 {
            -a
        }
    }

    #[derive(Associative)]
    struct Mul;
    impl BinaryOperator for Mul {
        type Domain = Reals;
        fn apply(a: i64, b: i64) -> i64 {
            a * b
        }
    }
    impl Identity for Mul {
        const IDENTITY: i64 = 1;
    }

    struct RealRing;
    impl SemiRing for RealRing {
        type Domain = Reals;
        type Addition = Add;
        type Multiplication = Mul;
    }

    #[derive(Debug)]
    struct Plane;
    impl Manifold for Plane {
        type Scalar = RealRing;
        type const DIM: usize = 2;
    }

    #[test]
    fn two_charts_on_the_plane() {
        let cartesian = Chart::<Plane>::new([Symbol::new("x"), Symbol::new("y")]);
        let polar = Chart::<Plane>::new([Symbol::new("r"), Symbol::new("θ")]);

        assert_eq!(
            cartesian.differential(0).unwrap(),
            DifferentialForm::Differential(Box::new(DifferentialForm::Function(Symbol::new("x"))))
        );
        assert_ne!(cartesian.differential(0), polar.differential(0));
    }

    #[test]
    fn substitute_replaces_coordinate_inside_differential() {
        let polar = Chart::<Plane>::new([Symbol::new("r"), Symbol::new("θ")]);
        // ω = r ∧ dθ, two free functions
        let mut omega = DifferentialForm::Wedged(vec![
            polar.coordinate(0).unwrap(),
            polar.differential(1).unwrap(),
        ]);
        assert_eq!(omega.degrees_of_freedom(), 2);

        // θ := 3  ⇒  r ∧ d3
        omega.substitute(Symbol::new("θ"), &DifferentialForm::Const(3));
        assert_eq!(
            omega,
            DifferentialForm::Wedged(vec![
                polar.coordinate(0).unwrap(),
                DifferentialForm::Differential(Box::new(DifferentialForm::Const(3))),
            ])
        );
        assert_eq!(omega.degrees_of_freedom(), 1);
    }
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
        let f = ExteriorFormatter::<Plane>::new();
        assert_eq!(
            f.format_expr(d(xy().differential(0).unwrap())),
            DifferentialForm::Const(0)
        );
        assert_eq!(
            f.format_expr(d(DifferentialForm::Const(7))),
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
        let f = ExteriorFormatter::<Plane>::new();
        // d(x ∧ dy) = dx ∧ dy
        assert_eq!(
            f.format_expr(d(wedge(vec![x, dy.clone()]))),
            wedge(vec![dx.clone(), dy.clone()])
        );
        // d(dx ∧ y) = -(dx ∧ dy), no reordering in the plain formatter
        assert_eq!(
            f.format_expr(d(wedge(vec![dx.clone(), y]))),
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
        let f = ExteriorFormatter::<Plane>::new();
        assert_eq!(
            f.format_expr(wedge(vec![dy.clone(), dx.clone()])),
            wedge(vec![dy.clone(), dx.clone()])
        );
        // 2 ∧ (x + dy) ∧ dx = 2 x ∧ dx + 2 dy ∧ dx
        let e = wedge(vec![
            DifferentialForm::Const(2),
            DifferentialForm::Add(vec![x.clone(), dy.clone()]),
            dx.clone(),
        ]);
        assert_eq!(
            f.format_expr(e),
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
        let f = GradedCommutativeFormatter::<Plane>::new();
        // dy ∧ dx = -(dx ∧ dy)
        assert_eq!(
            f.format_expr(wedge(vec![dy.clone(), dx.clone()])),
            wedge(vec![DifferentialForm::Const(-1), dx.clone(), dy.clone()])
        );
        // dx ∧ dx = 0
        assert_eq!(
            f.format_expr(wedge(vec![dx.clone(), dx.clone()])),
            DifferentialForm::Const(0)
        );
        // dx ∧ dy + dy ∧ dx = 0 ; dx ∧ dy + dx ∧ dy = 2 dx ∧ dy
        let a = wedge(vec![dx.clone(), dy.clone()]);
        let b = wedge(vec![dy.clone(), dx.clone()]);
        assert_eq!(
            f.format_expr(DifferentialForm::Add(vec![a.clone(), b])),
            DifferentialForm::Const(0)
        );
        assert_eq!(
            f.format_expr(DifferentialForm::Add(vec![a.clone(), a])),
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
            ExteriorFormatter::<Plane>::new().format_expr(top),
            DifferentialForm::Const(0)
        );
    }
}
