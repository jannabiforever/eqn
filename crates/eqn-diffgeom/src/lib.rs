// mgca: `Chart<M>` hold `M::DIM` coordinates.
#![feature(min_generic_const_args, macroless_generic_const_args)]
#![allow(incomplete_features)]

use std::collections::HashSet;

use eqn_algebra::ring::{DifferentialRing, Element};
use eqn_core::rewriter::Expression;
use eqn_core::symbol::Symbol;

pub const WEDGE_CHAR: char = '\u{2227}';
pub const PARTIAL_DIFFERENTIAL_CHAR: char = '\u{2202}';

/// A manifold is known to the library through its ring of functions.
pub trait Manifold {
    /// The ring of 0-forms, with `∂/∂xⁱ` along the coordinates a [`Chart`]
    /// names. A coordinate names a derivation *and* is a 0-form itself; the
    /// contract is `∂_i xʲ = δ_ij`.
    type Functions: DifferentialRing<Index: Clone + Into<Element<Self::Functions>>>;

    type const DIM: usize;
}

/// A 0-form on the manifold `M`: an element of `M::Functions`, represented
/// by an expression tree.
pub type ZeroForm<M> = Element<<M as Manifold>::Functions>;

/// A coordinate on the manifold `M`: names one of `M::Functions`'s
/// derivations. Only a diffgeom name for that ring's `Index`, not a
/// distinct type.
pub type Coordinate<M> = <<M as Manifold>::Functions as DifferentialRing>::Index;

#[derive_where::derive_where(Clone, Debug, Eq, PartialEq; ZeroForm<M>)]
pub enum DifferentialForm<M: Manifold> {
    /// A 0-form: any element of `M`'s ring of functions.
    Scalar(ZeroForm<M>),
    Neg(Box<Self>),
    Add(Vec<Self>),
    Wedged(Vec<Self>),
    Differential(Box<Self>),
}

/// Substitution is available whenever the 0-forms are themselves expression
/// trees; `Expression` is implemented on `DifferentialForm<M>` under that
/// condition.
impl<M: Manifold> Expression for DifferentialForm<M>
where
    ZeroForm<M>: Expression,
{
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

impl<M: Manifold> From<Symbol<<ZeroForm<M> as Expression>::Domain>> for DifferentialForm<M>
where
    ZeroForm<M>: Expression,
{
    fn from(value: Symbol<<ZeroForm<M> as Expression>::Domain>) -> Self {
        Self::Scalar(ZeroForm::<M>::from(value))
    }
}

/// A coordinate chart: names, for each position `i`, the derivation `∂_i`
/// and the coordinate function `xⁱ`. The contract is `∂_i xʲ = δ_ij`.
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
        self.coordinates
            .get(i)
            .cloned()
            .map(|c| DifferentialForm::Scalar(c.into()))
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
    use eqn_algebra::ring::{IntegerRing, PolynomialRing};
    use eqn_analysis::{ElementaryExpr, ElementaryFunctionRing, ElementaryRewriter};
    use eqn_core::rewriter::Rewriter;

    use super::*;

    #[derive(Debug)]
    pub(super) struct Plane;
    impl Manifold for Plane {
        type Functions = ElementaryFunctionRing<RationalField>;
        type const DIM: usize = 2;
    }

    #[derive(Debug)]
    pub(super) struct IntPlane;
    impl Manifold for IntPlane {
        type Functions = PolynomialRing<IntegerRing>;
        type const DIM: usize = 2;
    }

    fn constant(c: Rational) -> DifferentialForm<Plane> {
        DifferentialForm::Scalar(ElementaryExpr::Const(c))
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
        omega.substitute(Symbol::new("θ"), &constant(Rational::from(3)));
        assert_eq!(
            omega,
            DifferentialForm::Wedged(vec![
                polar.coordinate(0).unwrap(),
                DifferentialForm::Differential(Box::new(constant(Rational::from(3)))),
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
        omega.substitute(Symbol::new("y"), &constant(Rational::from(3)));
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
        let f = GradedCommutativeRewriter::<Plane, _>::new(xy.clone(), ElementaryRewriter::new());
        assert_eq!(f.rewrited_expr(omega), f.rewrited_expr(expected));
    }
}
