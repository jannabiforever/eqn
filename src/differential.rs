use crate::ring::{Ring, SemiRing};
use crate::set::Set;
use crate::symbol::Symbol;

pub const WEDGE_CHAR: char = '\u{2227}';
pub const PARTIAL_DIFFERENTIAL_CHAR: char = '\u{2202}';

/// a marker trait for smoothness.
///
/// NOTE: for now, it only support for real manifolds.
pub trait Manifold: Set {
    type Scalar: Ring;

    const DIM: usize;
}

pub enum DifferentialForm<M: Manifold> {
    Const(<<M::Scalar as SemiRing>::Domain as Set>::Element),
    Symbol(Symbol<M>),
    Differential(Symbol<M>),
    Neg(Box<DifferentialForm<M>>),
    Add(Vec<DifferentialForm<M>>),
    Wedged(Vec<DifferentialForm<M>>),
    Differentiated(Box<DifferentialForm<M>>),
}

impl<M: Manifold> PartialEq for DifferentialForm<M> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Const(a), Self::Const(b)) => a == b,
            (Self::Symbol(a), Self::Symbol(b)) => a == b,
            (Self::Differential(a), Self::Differential(b)) => a == b,
            (Self::Neg(a), Self::Neg(b)) => a == b,
            (Self::Add(a), Self::Add(b)) => a == b,
            (Self::Wedged(a), Self::Wedged(b)) => a == b,
            (Self::Differentiated(a), Self::Differentiated(b)) => a == b,
            _ => false,
        }
    }
}

impl<M: Manifold> Clone for DifferentialForm<M> {
    fn clone(&self) -> Self {
        match self {
            Self::Const(c) => Self::Const(c.clone()),
            Self::Symbol(symbol) => Self::Symbol(symbol.clone()),
            Self::Differential(symbol) => Self::Differential(symbol.clone()),
            Self::Neg(inner) => Self::Neg(inner.clone()),
            Self::Add(differential_forms) => Self::Add(differential_forms.clone()),
            Self::Wedged(differential_forms) => Self::Wedged(differential_forms.clone()),
            Self::Differentiated(differential_form) => {
                Self::Differentiated(differential_form.clone())
            }
        }
    }
}
