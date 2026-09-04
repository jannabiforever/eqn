// mgca: lets `Chart` carry `[_; M::DIM]` with `DIM` an associated const.
#![feature(min_generic_const_args, macroless_generic_const_args)]
#![allow(incomplete_features)]

use std::collections::HashSet;

use eqn_algebra::differential::DifferentialAlgebra;
use eqn_core::rewriter::Expression;
use eqn_core::set::Set;
use eqn_core::symbol::Symbol;

pub const WEDGE_CHAR: char = '\u{2227}';
pub const PARTIAL_DIFFERENTIAL_CHAR: char = '\u{2202}';

/// A manifold is known to the library through its ring of functions.
pub trait Manifold {
    /// The 0-forms `A`: a commutative `k`-algebra with partial derivatives
    /// along its coordinate symbols. Polynomials (`RingExpr`) give the
    /// algebraic de Rham complex over any commutative ring; elementary
    /// expressions (`eqn_analysis::ElementaryExpr`) give the smooth one
    /// over a field.
    type Functions: DifferentialAlgebra;

    type const DIM: usize;
}

/// A 0-form on `M`: any element of its ring of functions.
pub type ZeroForm<M> = <M as Manifold>::Functions;

/// A coordinate symbol on `M`, i.e. a name a 0-form can be built from.
pub type Coordinate<M> = Symbol<<ZeroForm<M> as Expression>::Domain>;

/// An element of the scalar ring of `M`.
pub type Scalar<M> = <<ZeroForm<M> as Expression>::Domain as Set>::Element;

/// `d` on a 0-form `e` is `Σ_i (∂e/∂xⁱ) dxⁱ` over a chart's coordinates
/// `xⁱ`; any other symbol appearing in `e` is a parameter, constant under
/// `d`. The rewriters in [`rewriter`] carry the chart that scopes the sum.
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq; ZeroForm<M>)]
pub enum DifferentialForm<M: Manifold> {
    /// A 0-form: any element of `M`'s ring of functions.
    Scalar(ZeroForm<M>),
    Neg(Box<Self>),
    Add(Vec<Self>),
    Wedged(Vec<Self>),
    Differential(Box<Self>),
}

impl<M: Manifold> DifferentialForm<M> {
    pub fn constant(c: Scalar<M>) -> Self {
        Self::Scalar(ZeroForm::<M>::constant(c))
    }
}

impl<M: Manifold> From<Coordinate<M>> for DifferentialForm<M> {
    fn from(value: Coordinate<M>) -> Self {
        Self::Scalar(ZeroForm::<M>::from(value))
    }
}

impl<M: Manifold> Expression for DifferentialForm<M> {
    type Domain = <ZeroForm<M> as Expression>::Domain;

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
            Self::Scalar(e) => e.as_symbol(),
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
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq; Coordinate<M>)]
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
    use eqn_algebra::ring::{IntegerRing, RingExpr};
    use eqn_analysis::ElementaryExpr;
    use eqn_core::rewriter::Rewriter;

    use super::*;

    #[derive(Debug)]
    pub(super) struct Plane;
    impl Manifold for Plane {
        type Functions = ElementaryExpr<RationalField>;
        type const DIM: usize = 2;
    }

    #[derive(Debug)]
    pub(super) struct IntPlane;
    impl Manifold for IntPlane {
        type Functions = RingExpr<IntegerRing>;
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
        let f = GradedCommutativeRewriter::<Plane>::new(xy.clone());
        assert_eq!(f.rewrited_expr(omega), f.rewrited_expr(expected));
    }
}
