use crate::ring::{Ring, SemiRing};
use crate::set::Set;
use crate::symbol::Symbol;

pub const WEDGE_CHAR: char = '\u{2227}';
pub const PARTIAL_DIFFERENTIAL_CHAR: char = '\u{2202}';

/// a marker trait for smoothness.
///
/// NOTE: for now, it only support for real manifolds.
pub trait Manifold {
    type Scalar: Ring;

    const DIM: usize;
}

/// An element of the scalar ring of `M`.
pub type Scalar<M> = <<<M as Manifold>::Scalar as SemiRing>::Domain as Set>::Element;

/// The set of 0-forms on `M`, i.e. smooth functions `M -> Scalar`.
/// Tags a [`Symbol`] as an unknown function rather than an unknown point.
pub struct ZeroForms<M: Manifold>(std::marker::PhantomData<M>);

impl<M: Manifold> Set for ZeroForms<M> {
    type Element = DifferentialForm<M>;
}

#[derive(Debug)]
pub enum DifferentialForm<M: Manifold> {
    Const(Scalar<M>),
    /// unknown `f: M -> Scalar`, a 0-form. coordinates are just functions:
    /// `dx` is `Differential(Function(x))`, and a chart is `DIM` of them.
    Function(Symbol<ZeroForms<M>>),
    Neg(Box<Self>),
    Add(Vec<Self>),
    Wedged(Vec<Self>),
    /// unevaluated `d`
    Differential(Box<Self>),
}

impl<M: Manifold> PartialEq for DifferentialForm<M> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Const(a), Self::Const(b)) => a == b,
            (Self::Function(a), Self::Function(b)) => a == b,
            (Self::Neg(a), Self::Neg(b)) => a == b,
            (Self::Add(a), Self::Add(b)) => a == b,
            (Self::Wedged(a), Self::Wedged(b)) => a == b,
            (Self::Differential(a), Self::Differential(b)) => a == b,
            _ => false,
        }
    }
}

impl<M: Manifold> Eq for DifferentialForm<M> {}

impl<M: Manifold> Clone for DifferentialForm<M> {
    fn clone(&self) -> Self {
        match self {
            Self::Const(c) => Self::Const(c.clone()),
            Self::Function(f) => Self::Function(f.clone()),
            Self::Neg(inner) => Self::Neg(inner.clone()),
            Self::Add(forms) => Self::Add(forms.clone()),
            Self::Wedged(forms) => Self::Wedged(forms.clone()),
            Self::Differential(form) => Self::Differential(form.clone()),
        }
    }
}

/// A coordinate chart: `M::DIM` distinct functions declared independent, so
/// their differentials `dx^i` form a basis of 1-forms. Several charts may
/// coexist on one manifold; relating them is a substitution rule, not a chart.
pub struct Chart<M: Manifold> {
    coordinates: Vec<Symbol<ZeroForms<M>>>,
}

impl<M: Manifold> Chart<M> {
    /// # Panics
    /// If the count is not `M::DIM` or two coordinates share a name.
    pub fn new(coordinates: impl Into<Vec<Symbol<ZeroForms<M>>>>) -> Self {
        let coordinates = coordinates.into();
        assert_eq!(
            coordinates.len(),
            M::DIM,
            "chart needs exactly DIM coordinates"
        );
        let mut names: Vec<_> = coordinates.iter().collect();
        names.sort();
        assert!(
            names.windows(2).all(|w| w[0] != w[1]),
            "chart coordinates must be distinct"
        );
        Self { coordinates }
    }

    pub fn coordinates(&self) -> &[Symbol<ZeroForms<M>>] {
        &self.coordinates
    }

    /// `x^i` as a 0-form.
    pub fn coordinate(&self, i: usize) -> DifferentialForm<M> {
        DifferentialForm::Function(self.coordinates[i].clone())
    }

    /// `dx^i`.
    pub fn differential(&self, i: usize) -> DifferentialForm<M> {
        DifferentialForm::Differential(Box::new(self.coordinate(i)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::op::{
        AssociativeOperator, BinaryOperator, CommutativeOperator, IdentityOperator, InverseOperator,
    };

    struct Reals;
    impl Set for Reals {
        type Element = i64; // ponytail: i64 stands in for R; swap for a real type when evaluation lands
    }

    struct Add;
    impl BinaryOperator for Add {
        type Domain = Reals;
        fn apply(a: i64, b: i64) -> i64 {
            a + b
        }
    }
    impl AssociativeOperator for Add {}
    impl CommutativeOperator for Add {}
    impl IdentityOperator for Add {
        const IDENTITY: i64 = 0;
    }
    impl InverseOperator for Add {
        fn inverse(a: i64) -> i64 {
            -a
        }
    }

    struct Mul;
    impl BinaryOperator for Mul {
        type Domain = Reals;
        fn apply(a: i64, b: i64) -> i64 {
            a * b
        }
    }
    impl AssociativeOperator for Mul {}
    impl IdentityOperator for Mul {
        const IDENTITY: i64 = 1;
    }

    struct RealRing;
    impl SemiRing for RealRing {
        type Domain = Reals;
        type Addition = Add;
        type Multiplication = Mul;
    }

    struct Plane;
    impl Manifold for Plane {
        type Scalar = RealRing;
        const DIM: usize = 2;
    }

    #[test]
    fn two_charts_on_the_plane() {
        let cartesian = Chart::<Plane>::new([Symbol::new("x"), Symbol::new("y")]);
        let polar = Chart::<Plane>::new([Symbol::new("r"), Symbol::new("θ")]);

        assert_eq!(
            cartesian.differential(0),
            DifferentialForm::Differential(Box::new(DifferentialForm::Function(Symbol::new("x"))))
        );
        assert_ne!(cartesian.differential(0), polar.differential(0));
    }

    #[test]
    #[should_panic]
    fn wrong_dimension_panics() {
        Chart::<Plane>::new([Symbol::new("x")]);
    }

    #[test]
    #[should_panic]
    fn duplicate_coordinate_panics() {
        Chart::<Plane>::new([Symbol::new("x"), Symbol::new("x")]);
    }
}
