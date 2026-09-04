// mgca: lets `Chart` carry `[_; M::DIM]` with `DIM` an associated const.
#![feature(min_generic_const_args, macroless_generic_const_args)]
#![allow(incomplete_features)]

use eqn_algebra::ring::{Ring, SemiRing};
use eqn_core::rewriter::Expression;
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

impl<M: Manifold> Expression for DifferentialForm<M> {
    type Domain = ZeroForms<M>;

    fn children(&self) -> &[Self] {
        match self {
            Self::Const(_) | Self::Function(_) => &[],
            Self::Neg(inner) | Self::Differential(inner) => std::slice::from_ref(inner),
            Self::Add(v) | Self::Wedged(v) => v,
        }
    }

    fn children_mut(&mut self) -> &mut [Self] {
        match self {
            Self::Const(_) | Self::Function(_) => &mut [],
            Self::Neg(inner) | Self::Differential(inner) => std::slice::from_mut(inner),
            Self::Add(v) | Self::Wedged(v) => v,
        }
    }

    fn as_symbol(&self) -> Option<&Symbol<Self::Domain>> {
        match self {
            Self::Function(f) => Some(f),
            _ => None,
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

mod rewriter;
pub use rewriter::{ExteriorRewriter, GradedCommutativeRewriter};

#[cfg(test)]
mod tests {
    use eqn_core::op::{Associative, BinaryOperator, Commutative};

    use super::*;

    #[derive(Set)]
    #[set(element = i64)] // ponytail: i64 stands in for R; swap for a real type when evaluation lands
    pub(super) struct Reals;

    #[derive(Associative, BinaryOperator, Commutative)]
    #[operator(domain = Reals, apply = |a, b| a + b, identity = 0, inverse = |a| -a)]
    pub(super) struct Add;

    #[derive(Associative, BinaryOperator)]
    #[operator(domain = Reals, apply = |a, b| a * b, identity = 1)]
    pub(super) struct Mul;

    pub(super) struct RealRing;
    impl SemiRing for RealRing {
        type Domain = Reals;
        type Addition = Add;
        type Multiplication = Mul;
    }

    #[derive(Debug)]
    pub(super) struct Plane;
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
}
