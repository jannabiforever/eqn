use std::collections::HashSet;

use crate::formatter::Expression;
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

    type const DIM: usize;
}

/// An element of the scalar ring of `M`.
pub type Scalar<M> = <<<M as Manifold>::Scalar as SemiRing>::Domain as Set>::Element;

/// The set of 0-forms on `M`, i.e. smooth functions `M -> Scalar`.
pub struct ZeroForms<M: Manifold>(std::marker::PhantomData<M>);

impl<M: Manifold> Set for ZeroForms<M> {
    type Element = Scalar<M>;
}

pub enum DifferentialForm<M: Manifold> {
    Const(Scalar<M>),
    /// unknown `f: M -> Scalar`, a 0-form.
    Function(Symbol<ZeroForms<M>>),
    Neg(Box<Self>),
    Add(Vec<Self>),
    Wedged(Vec<Self>),
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

impl<M: Manifold> std::fmt::Debug for DifferentialForm<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DifferentialForm::Const(c) => f.debug_tuple("Const").field(c).finish(),
            DifferentialForm::Function(symbol) => f.debug_tuple("Function").field(symbol).finish(),
            DifferentialForm::Neg(differential_form) => {
                f.debug_tuple("Neg").field(differential_form).finish()
            }
            DifferentialForm::Add(differential_forms) => {
                f.debug_tuple("Add").field(differential_forms).finish()
            }
            DifferentialForm::Wedged(differential_forms) => {
                f.debug_tuple("Wedged").field(differential_forms).finish()
            }
            DifferentialForm::Differential(differential_form) => f
                .debug_tuple("Differential")
                .field(differential_form)
                .finish(),
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
}
