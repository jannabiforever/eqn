// mgca: lets `Chart` carry `[_; M::DIM]` with `DIM` an associated const.
#![feature(min_generic_const_args, macroless_generic_const_args)]
#![allow(incomplete_features)]

use std::collections::HashSet;

use eqn_algebra::field::Field;
use eqn_algebra::ring::SemiRing;
use eqn_analysis::ElementaryExpr;
use eqn_core::rewriter::Expression;
use eqn_core::set::Set;
use eqn_core::symbol::Symbol;

pub const WEDGE_CHAR: char = '\u{2227}';
pub const PARTIAL_DIFFERENTIAL_CHAR: char = '\u{2202}';

/// a marker trait for smoothness.
///
/// NOTE: for now, it only support for real manifolds.
pub trait Manifold {
    type Scalar: Field;

    type const DIM: usize;
}

/// An element of the scalar field of `M`.
pub type Scalar<M> = <<<M as Manifold>::Scalar as SemiRing>::Domain as Set>::Element;

/// A coordinate symbol on `M`, i.e. a name a 0-form can be built from.
pub type Coordinate<M> = Symbol<<<M as Manifold>::Scalar as SemiRing>::Domain>;

/// A 0-form on `M`: any elementary expression in the coordinate symbols.
pub type ZeroForm<M> = ElementaryExpr<<M as Manifold>::Scalar>;

/// `d` on a 0-form `e` is `Σ_s (∂e/∂s) ds` over the free symbols of `e`, so
/// every symbol is treated as a coordinate and no chart is needed to
/// differentiate.
// ponytail: any symbol is a coordinate; a chart-scoped d can restrict the sum later
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq)]
pub enum DifferentialForm<M: Manifold> {
    /// A 0-form: any elementary expression in the coordinate symbols.
    Scalar(ZeroForm<M>),
    Neg(Box<Self>),
    Add(Vec<Self>),
    Wedged(Vec<Self>),
    Differential(Box<Self>),
}

impl<M: Manifold> DifferentialForm<M> {
    pub fn constant(c: Scalar<M>) -> Self {
        Self::Scalar(ElementaryExpr::Const(c))
    }
}

impl<M: Manifold> From<Coordinate<M>> for DifferentialForm<M> {
    fn from(value: Coordinate<M>) -> Self {
        Self::Scalar(ElementaryExpr::Symbol(value))
    }
}

impl<M: Manifold> Expression for DifferentialForm<M> {
    type Domain = <M::Scalar as SemiRing>::Domain;

    fn children(&self) -> &[Self] {
        match self {
            Self::Scalar(_) => &[],
            Self::Neg(inner) | Self::Differential(inner) => std::slice::from_ref(inner),
            Self::Add(v) | Self::Wedged(v) => v,
        }
    }

    fn children_mut(&mut self) -> &mut [Self] {
        match self {
            Self::Scalar(_) => &mut [],
            Self::Neg(inner) | Self::Differential(inner) => std::slice::from_mut(inner),
            Self::Add(v) | Self::Wedged(v) => v,
        }
    }

    fn as_symbol(&self) -> Option<&Symbol<Self::Domain>> {
        match self {
            Self::Scalar(ElementaryExpr::Symbol(s)) => Some(s),
            _ => None,
        }
    }

    /// A composite `Scalar` hides its symbols from the generic descendant
    /// walk, so this overrides the default: a coordinate can only be
    /// replaced by a 0-form, and the replacement happens inside the
    /// elementary expression tree.
    fn substitute(&mut self, sym: Symbol<Self::Domain>, expr: &Self) {
        if let Self::Scalar(e) = self {
            if let Self::Scalar(with) = expr {
                e.substitute(sym, with);
            }
            return;
        }
        for child in self.children_mut() {
            child.substitute(sym.clone(), expr);
        }
    }

    /// Overridden for the same reason as [`substitute`](Self::substitute):
    /// free symbols live inside each `Scalar` leaf's own expression tree.
    fn degrees_of_freedom(&self) -> usize {
        std::iter::once(self)
            .chain(self.descendants())
            .filter_map(|node| match node {
                Self::Scalar(e) => Some(e),
                _ => None,
            })
            .flat_map(|e| std::iter::once(e).chain(e.descendants()))
            .filter_map(Expression::as_symbol)
            .collect::<HashSet<_>>()
            .len()
    }
}

/// A coordinate chart
pub struct Chart<M: Manifold> {
    coordinates: [Coordinate<M>; M::DIM],
}

impl<M: Manifold> Chart<M> {
    pub fn new(coordinates: [Coordinate<M>; M::DIM]) -> Self {
        Self { coordinates }
    }

    pub fn coordinates(&self) -> &[Coordinate<M>; M::DIM] {
        &self.coordinates
    }

    /// `x^i` as a 0-form.
    pub fn coordinate(&self, i: usize) -> Option<DifferentialForm<M>> {
        self.coordinates.get(i).cloned().map(DifferentialForm::from)
    }

    /// `dx^i`.
    pub fn differential(&self, i: usize) -> Option<DifferentialForm<M>> {
        self.coordinate(i)
            .map(|c| DifferentialForm::Differential(Box::new(c)))
    }
}

mod rewriter;
pub use rewriter::{ExteriorRewriter, GradedCommutativeRewriter};

#[cfg(test)]
mod tests {
    use eqn_algebra::field::{Rational, RationalField};
    use eqn_core::rewriter::Rewriter;

    use super::*;

    #[derive(Debug)]
    pub(super) struct Plane;
    impl Manifold for Plane {
        type Scalar = RationalField;
        type const DIM: usize = 2;
    }

    #[test]
    fn two_charts_on_the_plane() {
        let cartesian = Chart::<Plane>::new([Symbol::new("x"), Symbol::new("y")]);
        let polar = Chart::<Plane>::new([Symbol::new("r"), Symbol::new("θ")]);

        assert_eq!(
            cartesian.differential(0).unwrap(),
            DifferentialForm::Differential(Box::new(DifferentialForm::Scalar(
                ElementaryExpr::Symbol(Symbol::new("x"))
            )))
        );
        assert_ne!(cartesian.differential(0), polar.differential(0));
    }

    #[test]
    fn substitute_replaces_coordinate_inside_differential() {
        let polar = Chart::<Plane>::new([Symbol::new("r"), Symbol::new("θ")]);
        // ω = r ∧ dθ, two free symbols
        let mut omega = DifferentialForm::Wedged(vec![
            polar.coordinate(0).unwrap(),
            polar.differential(1).unwrap(),
        ]);
        assert_eq!(omega.degrees_of_freedom(), 2);

        // θ := 3  ⇒  r ∧ d3
        omega.substitute(
            Symbol::new("θ"),
            &DifferentialForm::constant(Rational::from(3)),
        );
        assert_eq!(
            omega,
            DifferentialForm::Wedged(vec![
                polar.coordinate(0).unwrap(),
                DifferentialForm::Differential(Box::new(DifferentialForm::constant(
                    Rational::from(3)
                ))),
            ])
        );
        assert_eq!(omega.degrees_of_freedom(), 1);
    }

    #[test]
    fn substitute_into_composite_scalar_updates_degrees_of_freedom() {
        let xy = Chart::<Plane>::new([Symbol::new("x"), Symbol::new("y")]);
        let x = || ElementaryExpr::Symbol(Symbol::new("x"));
        let y = || ElementaryExpr::Symbol(Symbol::new("y"));

        // ω = (x^2 + y) dx
        let coeff = ElementaryExpr::Add(vec![
            ElementaryExpr::Pow {
                base: Box::new(x()),
                exponent: 2,
            },
            y(),
        ]);
        let mut omega = DifferentialForm::Wedged(vec![
            DifferentialForm::Scalar(coeff),
            xy.differential(0).unwrap(),
        ]);
        assert_eq!(omega.degrees_of_freedom(), 2);

        // y := 3  ⇒  (x^2 + 3) dx
        omega.substitute(
            Symbol::new("y"),
            &DifferentialForm::constant(Rational::from(3)),
        );
        assert_eq!(omega.degrees_of_freedom(), 1);

        let expected = DifferentialForm::Wedged(vec![
            DifferentialForm::Scalar(ElementaryExpr::Add(vec![
                ElementaryExpr::Pow {
                    base: Box::new(x()),
                    exponent: 2,
                },
                ElementaryExpr::Const(Rational::from(3)),
            ])),
            xy.differential(0).unwrap(),
        ]);

        // `substitute` does not normalize; compare after normalizing both sides.
        let f = GradedCommutativeRewriter::<Plane>::new();
        assert_eq!(f.rewrited_expr(omega), f.rewrited_expr(expected));
    }
}
