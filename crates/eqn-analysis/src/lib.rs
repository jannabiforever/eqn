// NOTE: `eqn_core::rewriter` is not re-exported here (unlike `set`/`symbol`)
// because it would collide with this crate's own private `rewriter` module
// below.
use std::ops::{Add, Mul, Neg};

use eqn_algebra::differential::DifferentialAlgebra;
use eqn_algebra::field::Field;
use eqn_core::rewriter::Expression;
use eqn_core::set::Set;
use eqn_core::symbol::Symbol;
pub use eqn_core::{set, symbol};

/// Elementary transcendental functions.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Elementary {
    Exp,
    Log,
    Sin,
    Cos,
}

/// An expression tree over a field, closed under the elementary functions
/// and differentiation. `Pow` takes any integer exponent, so `x^-1` is
/// division. `D` is the unevaluated derivative `d(inner)/d(wrt)`; the
/// rewriter eliminates it.
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq)]
pub enum ElementaryExpr<F: Field> {
    Const(<F::Domain as Set>::Element),
    Symbol(Symbol<F::Domain>),
    Neg(Box<Self>),
    Add(Vec<Self>),
    Mul(Vec<Self>),
    Pow {
        base: Box<Self>,
        exponent: isize,
    },
    Fn(Elementary, Box<Self>),
    D {
        wrt: Symbol<F::Domain>,
        inner: Box<Self>,
    },
}

impl<F: Field> ElementaryExpr<F> {
    pub fn elementary(kind: Elementary, arg: Self) -> Self {
        Self::Fn(kind, Box::new(arg))
    }

    pub fn d(wrt: Symbol<F::Domain>, inner: Self) -> Self {
        Self::D {
            wrt,
            inner: Box::new(inner),
        }
    }
}

impl<F: Field> Expression for ElementaryExpr<F> {
    type Domain = F::Domain;

    fn children(&self) -> &[Self] {
        match self {
            Self::Const(_) | Self::Symbol(_) => &[],
            Self::Neg(inner) | Self::Pow { base: inner, .. } | Self::Fn(_, inner) => {
                std::slice::from_ref(inner)
            }
            Self::D { inner, .. } => std::slice::from_ref(inner),
            Self::Add(v) | Self::Mul(v) => v,
        }
    }

    fn children_mut(&mut self) -> &mut [Self] {
        match self {
            Self::Const(_) | Self::Symbol(_) => &mut [],
            Self::Neg(inner) | Self::Pow { base: inner, .. } | Self::Fn(_, inner) => {
                std::slice::from_mut(inner)
            }
            Self::D { inner, .. } => std::slice::from_mut(inner),
            Self::Add(v) | Self::Mul(v) => v,
        }
    }

    fn as_symbol(&self) -> Option<&Symbol<Self::Domain>> {
        match self {
            Self::Symbol(s) => Some(s),
            _ => None,
        }
    }
}

impl<F: Field> From<Symbol<F::Domain>> for ElementaryExpr<F> {
    fn from(value: Symbol<F::Domain>) -> Self {
        Self::Symbol(value)
    }
}

/// Symbolic; builds the tree, does not normalize.
impl<F: Field> Add for ElementaryExpr<F> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self::Add(vec![self, rhs])
    }
}

/// Symbolic; builds the tree, does not normalize.
impl<F: Field> Mul for ElementaryExpr<F> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        Self::Mul(vec![self, rhs])
    }
}

/// Symbolic; builds the tree, does not normalize.
impl<F: Field> Neg for ElementaryExpr<F> {
    type Output = Self;

    fn neg(self) -> Self {
        Self::Neg(Box::new(self))
    }
}

mod rewriter;
pub use rewriter::ElementaryRewriter;

impl<F: Field> DifferentialAlgebra for ElementaryExpr<F> {
    type Constants = F;
    type Normalizer = ElementaryRewriter<F>;

    fn constant(c: <Self::Domain as Set>::Element) -> Self {
        Self::Const(c)
    }

    fn as_constant(&self) -> Option<&<Self::Domain as Set>::Element> {
        match self {
            Self::Const(c) => Some(c),
            _ => None,
        }
    }

    /// The eager form of [`ElementaryExpr::D`]: both funnel through
    /// [`rewriter::derivative`], the same symbolic differentiation the
    /// rewriter uses to eliminate `D` nodes.
    fn partial(self, wrt: &Symbol<Self::Domain>) -> Self {
        rewriter::derivative(self, wrt)
    }
}
