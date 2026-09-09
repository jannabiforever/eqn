use eqn_core::op::{Associative, BinaryOperator, Identity};
use eqn_core::rewriter::Expression;
use eqn_core::set::{Elem, Set};
use eqn_core::symbol::Symbol;

mod parse;
mod rewriter;

// Re-exports
pub use rewriter::{CommutativeMonoidRewriter, NonCommutativeMonoidRewriter};

/// An element of a monoid.
pub type MonoidElem<M> = Elem<<M as Monoid>::Domain>;

/// A monoid: a domain paired with an associative operator that has an
/// identity element. Both laws are demanded as bounds, so an operator
/// must declare them to qualify.
pub trait Monoid {
    type Domain: Set;
    type Operator: BinaryOperator<Domain = Self::Domain> + Associative + Identity;

    const IDENTITY: MonoidElem<Self> = <Self::Operator as Identity>::IDENTITY;

    fn apply(lhs: MonoidElem<Self>, rhs: MonoidElem<Self>) -> MonoidElem<Self> {
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

/// A subset containing the identity and closed under the monoid operation.
pub trait Submonoid {
    type Parent: Monoid;

    fn contains(value: &MonoidElem<Self::Parent>) -> bool;
}

/// An expression tree over a monoid: constants, named symbols, and n-ary
/// applications of the monoid's operator.
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq)]
pub enum MonoidExpr<M: Monoid> {
    Const(MonoidElem<M>),
    Symbol(Symbol<M::Domain>),
    Op(Vec<MonoidExpr<M>>),
}

impl<M: Monoid> MonoidExpr<M> {
    /// Wraps a domain element as a constant expression.
    #[inline]
    pub const fn constant(value: MonoidElem<M>) -> Self {
        Self::Const(value)
    }
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

impl<D: Set, M: Monoid<Domain = D>> From<Symbol<D>> for MonoidExpr<M> {
    fn from(value: Symbol<D>) -> Self {
        Self::Symbol(value)
    }
}

#[cfg(test)]
mod tests {
    use eqn_core::set::Z;

    use super::*;
    use crate::operator_impl::ZAdd;

    type IntegerAddition = (Z, ZAdd);

    struct NonnegativeIntegers;

    impl Submonoid for NonnegativeIntegers {
        type Parent = IntegerAddition;

        fn contains(value: &MonoidElem<Self::Parent>) -> bool {
            *value >= 0
        }
    }

    #[test]
    fn nonnegative_integers_form_a_submonoid() {
        assert!(NonnegativeIntegers::contains(&IntegerAddition::IDENTITY));

        for lhs in [0, 1, 4, 9] {
            for rhs in [0, 2, 5, 8] {
                assert!(NonnegativeIntegers::contains(&IntegerAddition::apply(
                    lhs, rhs
                )));
            }
        }
    }
}
