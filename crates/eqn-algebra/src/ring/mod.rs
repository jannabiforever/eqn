use std::num::NonZeroUsize;

use eqn_core::op::{Associative, BinaryOperator, Commutative, Identity, Inverse};
use eqn_core::rewriter::Expression;
use eqn_core::set::{Set, Subset};
use eqn_core::symbol::Symbol;

pub mod differential;
pub mod ideal;
mod parse;
pub mod quotient;
pub mod rewriter;

// ================================================================================
// Ring
// ================================================================================

/// Alias for Ring's domain.
pub type RingElem<S> = <S as SemiRing>::Domain;

/// Alias for Ring's add operation
pub type RingAdd<S> = <S as SemiRing>::Addition;

/// Alias for Ring's mul operation
pub type RingMul<S> = <S as SemiRing>::Multiplication;

/// A semi-ring: addition forms a commutative monoid, multiplication forms a
/// monoid. Distributivity and annihilation (`0 * a = 0`) relate the two
/// operators and cannot be encoded as bounds; they are part of the contract.
pub trait SemiRing {
    type Domain: Set;

    /// The addition operator for this semi-ring.
    ///
    /// Should be associative, commutative, and have an identity element.
    type Addition: BinaryOperator<Domain = Self::Domain> + Associative + Commutative + Identity;

    /// The multiplication operator for this semi-ring.
    ///
    /// Should be associative and have an identity element.
    type Multiplication: BinaryOperator<Domain = Self::Domain> + Associative + Identity;

    /// Addition's identity
    fn zero() -> RingElem<Self> {
        <Self::Addition as Identity>::identity()
    }

    /// Multiplication's identity
    fn one() -> RingElem<Self> {
        <Self::Multiplication as Identity>::identity()
    }

    /// Source spelling of addition.
    const ADD_SYMBOL: &'static str = <Self::Addition as BinaryOperator>::SYMBOL;

    /// Source spelling of multiplication.
    const MUL_SYMBOL: &'static str = <Self::Multiplication as BinaryOperator>::SYMBOL;

    fn add(a: RingElem<Self>, b: RingElem<Self>) -> RingElem<Self> {
        <Self::Addition as BinaryOperator>::apply(a, b)
    }

    fn multiply(a: RingElem<Self>, b: RingElem<Self>) -> RingElem<Self> {
        <Self::Multiplication as BinaryOperator>::apply(a, b)
    }

    /// `n * ONE`: the image of `n` under the unique semi-ring map from the
    /// naturals, computed by double-and-add in `O(log n)` additions.
    fn from_usize(mut n: usize) -> RingElem<Self> {
        let mut acc = Self::zero();
        let mut power = Self::one();
        while n > 0 {
            if n & 1 == 1 {
                acc = Self::add(acc, power.clone());
            }
            n >>= 1;
            if n > 0 {
                power = Self::add(power.clone(), power);
            }
        }
        acc
    }
}

/// A semi-ring is an addition and a multiplication on one domain, as a pair.
impl<A, M> SemiRing for (A, M)
where
    A: BinaryOperator + Associative + Commutative + Identity,
    M: BinaryOperator<Domain = A::Domain> + Associative + Identity,
{
    type Domain = A::Domain;
    type Addition = A;
    type Multiplication = M;
}

/// A subset containing zero and one and closed under addition and
/// multiplication.
pub trait SubSemiRing: Subset<Superset = RingElem<Self::Parent>> {
    type Parent: SemiRing;
}

/// A ring: a semi-ring whose addition also has inverses.
pub trait Ring: SemiRing<Addition: Inverse> {
    /// Source spelling of subtraction and negation.
    const SUB_SYMBOL: &'static str = <Self::Addition as Inverse>::INVERSE_SYMBOL;

    /// The additive inverse.
    fn negate(a: RingElem<Self>) -> RingElem<Self>;
}

/// Any semi-ring with invertible addition is a ring for free.
impl<SR: SemiRing> Ring for SR
where
    SR::Addition: Inverse,
{
    fn negate(a: RingElem<Self>) -> RingElem<Self> {
        <SR::Addition as Inverse>::inverse(a)
    }
}

/// A unital subsemiring of a ring that is closed under additive inverses.
pub trait Subring: SubSemiRing<Parent: Ring> {}

/// A ring whose multiplication is also commutative.
///
/// In addition to the ring laws, `a * b` must equal `b * a` for every pair of
/// elements in the domain. [`Commutative`] declares this law.
pub trait CommutativeRing: Ring<Multiplication: Commutative> {}

/// Classifies every ring with a commutative multiplication as a commutative
/// ring.
impl<R> CommutativeRing for R
where
    R: Ring,
    R::Multiplication: Commutative,
{
}

/// An expression tree over a semi-ring: constants, named symbols, n-ary sums
/// and products, and powers (repeated multiplication, exponent >= 1).
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq)]
pub enum SemiRingExpr<SR: SemiRing> {
    Const(SR::Domain),
    Symbol(Symbol<SR::Domain>),
    Add(Vec<SemiRingExpr<SR>>),
    Mul(Vec<SemiRingExpr<SR>>),
    Pow {
        base: Box<SemiRingExpr<SR>>,
        exponent: NonZeroUsize,
    },
}

impl<SR: SemiRing> Expression for SemiRingExpr<SR> {
    type Domain = SR::Domain;

    fn children(&self) -> &[Self] {
        match self {
            Self::Const(_) | Self::Symbol(_) => &[],
            Self::Pow { base, .. } => std::slice::from_ref(base),
            Self::Add(v) | Self::Mul(v) => v,
        }
    }

    fn children_mut(&mut self) -> &mut [Self] {
        match self {
            Self::Const(_) | Self::Symbol(_) => &mut [],
            Self::Pow { base, .. } => std::slice::from_mut(base),
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

impl<D: Set, SR: SemiRing<Domain = D>> From<Symbol<D>> for SemiRingExpr<SR> {
    fn from(value: Symbol<D>) -> Self {
        Self::Symbol(value)
    }
}

// ================================================================================
// Ring expressions
// ================================================================================

/// An expression tree over a ring; `Neg` is the additive inverse, which is
/// what distinguishes it from [`SemiRingExpr`].
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq)]
pub enum RingExpr<R: Ring> {
    Const(R::Domain),
    Symbol(Symbol<R::Domain>),
    Neg(Box<RingExpr<R>>),
    Add(Vec<RingExpr<R>>),
    Mul(Vec<RingExpr<R>>),
    Pow {
        base: Box<RingExpr<R>>,
        exponent: NonZeroUsize,
    },
}

impl<R: Ring> Expression for RingExpr<R> {
    type Domain = R::Domain;

    fn children(&self) -> &[Self] {
        match self {
            Self::Const(_) | Self::Symbol(_) => &[],
            Self::Neg(inner) | Self::Pow { base: inner, .. } => std::slice::from_ref(inner),
            Self::Add(v) | Self::Mul(v) => v,
        }
    }

    fn children_mut(&mut self) -> &mut [Self] {
        match self {
            Self::Const(_) | Self::Symbol(_) => &mut [],
            Self::Neg(inner) | Self::Pow { base: inner, .. } => std::slice::from_mut(inner),
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

impl<R: Ring> From<Symbol<R::Domain>> for RingExpr<R> {
    fn from(sym: Symbol<R::Domain>) -> Self {
        Self::Symbol(sym)
    }
}

/// Lowers to the semi-ring tree by encoding `Neg(x)` as `(-1) * x`
/// (`-1` = the additive inverse of one, which is central in every ring).
impl<R: Ring> From<RingExpr<R>> for SemiRingExpr<R> {
    fn from(expr: RingExpr<R>) -> Self {
        match expr {
            RingExpr::Const(c) => Self::Const(c),
            RingExpr::Symbol(s) => Self::Symbol(s),
            RingExpr::Neg(inner) => {
                Self::Mul(vec![Self::Const(R::negate(R::one())), (*inner).into()])
            }
            RingExpr::Add(v) => Self::Add(v.into_iter().map(Into::into).collect()),
            RingExpr::Mul(v) => Self::Mul(v.into_iter().map(Into::into).collect()),
            RingExpr::Pow { base, exponent } => Self::Pow {
                base: Box::new((*base).into()),
                exponent,
            },
        }
    }
}

impl<R: Ring> From<SemiRingExpr<R>> for RingExpr<R> {
    fn from(expr: SemiRingExpr<R>) -> Self {
        match expr {
            SemiRingExpr::Const(c) => Self::Const(c),
            SemiRingExpr::Symbol(s) => Self::Symbol(s),
            SemiRingExpr::Add(v) => Self::Add(v.into_iter().map(Into::into).collect()),
            SemiRingExpr::Mul(v) => Self::Mul(v.into_iter().map(Into::into).collect()),
            SemiRingExpr::Pow { base, exponent } => Self::Pow {
                base: Box::new((*base).into()),
                exponent,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use eqn_core::set::Z;

    use super::*;
    use crate::operator_impl::{ZAdd, ZMul};

    type Integers = (ZAdd, ZMul);

    struct NonnegativeIntegers;

    impl Subset for NonnegativeIntegers {
        type Superset = Z;

        fn contains(value: &i64) -> bool {
            *value >= 0
        }
    }

    impl SubSemiRing for NonnegativeIntegers {
        type Parent = Integers;
    }

    struct AllIntegers;

    impl Subset for AllIntegers {
        type Superset = Z;

        fn contains(_: &i64) -> bool {
            true
        }
    }

    impl SubSemiRing for AllIntegers {
        type Parent = Integers;
    }

    impl Subring for AllIntegers {}

    #[test]
    fn nonnegative_integers_form_a_subsemiring() {
        assert!(NonnegativeIntegers::contains(&Integers::zero()));
        assert!(NonnegativeIntegers::contains(&Integers::one()));

        for lhs in [0, 1, 4, 9] {
            for rhs in [0, 2, 5, 8] {
                assert!(NonnegativeIntegers::contains(&Integers::add(lhs, rhs)));
                assert!(NonnegativeIntegers::contains(&Integers::multiply(lhs, rhs)));
            }
        }
    }

    #[test]
    fn integers_form_a_subring() {
        for value in [-10, -1, 0, 1, 10] {
            assert!(AllIntegers::contains(&Integers::negate(value)));
        }
    }
}
