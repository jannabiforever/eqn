use eqn_core::op::{Associative, BinaryOperator, Identity};
use eqn_core::rewriter::Expression;
use eqn_core::set::{Set, Subset};
use eqn_core::symbol::Symbol;

mod parse;
pub mod rewriter;

/// An element of a monoid.
pub type MonoidElem<M> = <M as Monoid>::Domain;

/// A monoid: a domain paired with an associative operator that has an
/// identity element. Both laws are demanded as bounds, so an operator
/// must declare them to qualify.
pub trait Monoid {
    type Domain: Set;
    type Operator: BinaryOperator<Domain = Self::Domain> + Associative + Identity;

    fn identity() -> MonoidElem<Self> {
        <Self::Operator as Identity>::identity()
    }

    /// Source spelling of the operation.
    const SYMBOL: &'static str = <Self::Operator as BinaryOperator>::SYMBOL;

    fn apply(lhs: MonoidElem<Self>, rhs: MonoidElem<Self>) -> MonoidElem<Self> {
        <Self::Operator as BinaryOperator>::apply(lhs, rhs)
    }
}

/// A monoid is one associative operation with an identity, as a one-tuple;
/// its domain is the operation's.
impl<Op> Monoid for (Op,)
where
    Op: BinaryOperator + Associative + Identity,
{
    type Domain = Op::Domain;
    type Operator = Op;
}

/// A subset containing the identity and closed under the monoid operation.
pub trait Submonoid: Subset<Superset = <Self::Parent as Monoid>::Domain> {
    type Parent: Monoid;
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
    pub const fn constant(value: M::Domain) -> Self {
        Self::Const(value)
    }

    pub fn apply(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Self::Op(mut lhs), Self::Op(rhs)) => {
                lhs.extend(rhs);
                Self::Op(lhs)
            }
            (Self::Op(mut lhs), rhs) => {
                lhs.push(rhs);
                Self::Op(lhs)
            }
            (lhs, Self::Op(rhs)) => {
                let mut v = vec![lhs];
                v.extend(rhs);
                Self::Op(v)
            }
            (lhs, rhs) => Self::Op(vec![lhs, rhs]),
        }
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

    type IntegerAddition = (ZAdd,);

    struct NonnegativeIntegers;

    impl Subset for NonnegativeIntegers {
        type Superset = Z;

        fn contains(value: &Z) -> bool {
            *value >= Z::ZERO
        }
    }

    impl Submonoid for NonnegativeIntegers {
        type Parent = IntegerAddition;
    }

    #[test]
    fn nonnegative_integers_form_a_submonoid() {
        assert!(NonnegativeIntegers::contains(&IntegerAddition::identity()));

        for lhs in [0, 1, 4, 9].map(Z::from) {
            for rhs in [0, 2, 5, 8].map(Z::from) {
                assert!(NonnegativeIntegers::contains(&IntegerAddition::apply(
                    lhs.clone(),
                    rhs
                )));
            }
        }
    }
}
