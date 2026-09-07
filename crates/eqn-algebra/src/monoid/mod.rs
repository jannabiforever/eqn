use crate::op::{Associative, BinaryOperator, Identity};
use crate::rewriter::Expression;
use crate::set::Set;
use crate::symbol::Symbol;

/// A monoid: a domain paired with an associative operator that has an
/// identity element. Both laws are demanded as bounds, so an operator
/// must declare them to qualify.
pub trait Monoid {
    type Domain: Set;
    type Operator: BinaryOperator<Domain = Self::Domain> + Associative + Identity;

    const IDENTITY: <Self::Domain as Set>::Element = <Self::Operator as Identity>::IDENTITY;

    fn apply(
        lhs: <Self::Domain as Set>::Element,
        rhs: <Self::Domain as Set>::Element,
    ) -> <Self::Domain as Set>::Element {
        <Self::Operator as BinaryOperator>::apply(lhs, rhs)
    }
}

/// Any (domain, operator) pair forms a monoid for free.
impl<D, Op> Monoid for (D, Op)
where
    D: Set,
    Op: BinaryOperator<Domain = D> + Associative + Identity,
{
    type Domain = D;
    type Operator = Op;
}

/// An expression tree over a monoid: constants, named symbols, and n-ary
/// applications of the monoid's operator.
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq)]
pub enum MonoidExpr<M: Monoid> {
    Const(<M::Domain as Set>::Element),
    Symbol(Symbol<M::Domain>),
    Op(Vec<MonoidExpr<M>>),
}

impl<M: Monoid> Expression for MonoidExpr<M> {
    type Domain = M::Domain;

    fn children(&self) -> &[Self] {
        match self {
            Self::Const(_) | Self::Symbol(_) => &[],
            Self::Op(v) => v,
        }
    }

    fn children_mut(&mut self) -> &mut [Self] {
        match self {
            Self::Const(_) | Self::Symbol(_) => &mut [],
            Self::Op(v) => v,
        }
    }

    fn as_symbol(&self) -> Option<&Symbol<Self::Domain>> {
        match self {
            Self::Symbol(s) => Some(s),
            _ => None,
        }
    }
}

impl<M: Monoid> MonoidExpr<M> {
    /// Wraps a domain element as a constant expression.
    #[inline]
    pub const fn constant(value: <M::Domain as Set>::Element) -> Self {
        Self::Const(value)
    }
}

impl<D: Set, M: Monoid<Domain = D>> From<Symbol<D>> for MonoidExpr<M> {
    fn from(value: Symbol<D>) -> Self {
        Self::Symbol(value)
    }
}

mod rewriter;
pub use rewriter::{CommutativeMonoidRewriter, NonCommutativeMonoidRewriter};
