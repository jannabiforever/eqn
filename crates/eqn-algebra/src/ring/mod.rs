use std::marker::PhantomData;
use std::num::NonZeroUsize;

use crate::op::{Associative, BinaryOperator, Commutative, Identity, Inverse};
use crate::rewriter::Expression;
use crate::set::Set;
use crate::symbol::Symbol;

// ================================================================================
// Ring
// ================================================================================

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

    const ZERO: <Self::Domain as Set>::Element = <Self::Addition as Identity>::IDENTITY;

    const ONE: <Self::Domain as Set>::Element = <Self::Multiplication as Identity>::IDENTITY;

    fn add(
        a: <Self::Domain as Set>::Element,
        b: <Self::Domain as Set>::Element,
    ) -> <Self::Domain as Set>::Element {
        <Self::Addition as BinaryOperator>::apply(a, b)
    }

    fn multiply(
        a: <Self::Domain as Set>::Element,
        b: <Self::Domain as Set>::Element,
    ) -> <Self::Domain as Set>::Element {
        <Self::Multiplication as BinaryOperator>::apply(a, b)
    }

    /// `n · ONE`: the image of `n` under the unique semi-ring map from the
    /// naturals, computed by double-and-add in `O(log n)` additions.
    fn from_usize(mut n: usize) -> <Self::Domain as Set>::Element {
        let mut acc = Self::ZERO;
        let mut power = Self::ONE;
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

/// A ring: a semi-ring whose addition also has inverses.
pub trait Ring: SemiRing {
    /// The additive inverse.
    fn negate(a: <Self::Domain as Set>::Element) -> <Self::Domain as Set>::Element;
}

/// Any semi-ring with invertible addition is a ring for free.
impl<SR: SemiRing> Ring for SR
where
    SR::Addition: Inverse,
{
    fn negate(a: <Self::Domain as Set>::Element) -> <Self::Domain as Set>::Element {
        <SR::Addition as Inverse>::inverse(a)
    }
}

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
    Const(<SR::Domain as Set>::Element),
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
    Const(<R::Domain as Set>::Element),
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
                Self::Mul(vec![Self::Const(R::negate(R::ONE)), (*inner).into()])
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

/// Symbolic; builds the tree, does not normalize.
impl<R: Ring> std::ops::Add for RingExpr<R> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self::Add(vec![self, rhs])
    }
}

/// Symbolic; builds the tree, does not normalize.
impl<R: Ring> std::ops::Mul for RingExpr<R> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        Self::Mul(vec![self, rhs])
    }
}

/// Symbolic; builds the tree, does not normalize.
impl<R: Ring> std::ops::Neg for RingExpr<R> {
    type Output = Self;

    fn neg(self) -> Self {
        Self::Neg(Box::new(self))
    }
}

// ================================================================================
// PolynomialRing: the ring formed by RingExpr trees
// ================================================================================

/// The set of polynomial expressions over `R`, represented by [`RingExpr`]
/// trees.
#[derive(Set)]
#[set(element = RingExpr<R>)]
pub struct Polynomials<R: Ring>(PhantomData<R>);

/// Symbolic addition: builds the tree, does not normalize.
#[derive(Associative, BinaryOperator, Commutative)]
#[operator(
    domain = Polynomials<R>,
    apply = |a, b| RingExpr::Add(vec![a, b]),
    identity = RingExpr::Const(R::ZERO),
    inverse = |a| RingExpr::Neg(Box::new(a))
)]
pub struct PolynomialAdd<R: Ring>(PhantomData<R>);

/// Symbolic multiplication: builds the tree, does not normalize.
#[derive(Associative, BinaryOperator, Commutative)]
#[operator(
    domain = Polynomials<R>,
    apply = |a, b| RingExpr::Mul(vec![a, b]),
    identity = RingExpr::Const(R::ONE)
)]
pub struct PolynomialMul<R: CommutativeRing>(PhantomData<R>);

/// The commutative ring of polynomials over `R`. Elements are trees, so `Eq`
/// is structural: the ring laws hold modulo [`CommutativeRingRewriter`].
pub struct PolynomialRing<R: CommutativeRing>(PhantomData<R>);

impl<R: CommutativeRing> SemiRing for PolynomialRing<R> {
    type Domain = Polynomials<R>;
    type Addition = PolynomialAdd<R>;
    type Multiplication = PolynomialMul<R>;
}

mod rewriter;
pub use rewriter::{CommutativeRingRewriter, RingRewriter, SemiRingRewriter};

// ================================================================================
// Integers: the canonical test ring
// ================================================================================

#[derive(Set)]
#[set(element = i64)]
pub struct Integers;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Integers, apply = |a, b| a + b, identity = 0, inverse = |a| -a)]
pub struct IntegerAdd;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Integers, apply = |a, b| a * b, identity = 1)]
pub struct IntegerMul;

/// The canonical test ring. Not a field: `IntegerMul` has no `Inverse`.
pub struct IntegerRing;

impl SemiRing for IntegerRing {
    type Domain = Integers;
    type Addition = IntegerAdd;
    type Multiplication = IntegerMul;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_usize_is_the_natural_map() {
        for n in [0usize, 1, 2, 3, 7, 8, 1000] {
            assert_eq!(IntegerRing::from_usize(n), n as i64);
        }
    }

    #[test]
    fn polynomial_ring_operators_build_trees() {
        type P = PolynomialRing<IntegerRing>;
        let x = RingExpr::<IntegerRing>::Symbol(Symbol::new("x"));
        let y = RingExpr::<IntegerRing>::Symbol(Symbol::new("y"));

        assert_eq!(
            P::add(x.clone(), y.clone()),
            RingExpr::Add(vec![x.clone(), y])
        );
        assert_eq!(P::ONE, RingExpr::Const(1));
        assert_eq!(P::negate(x.clone()), RingExpr::Neg(Box::new(x)));
    }

    #[test]
    fn polynomial_ring_is_commutative() {
        fn assert_commutative_ring<R: CommutativeRing>() {}
        assert_commutative_ring::<PolynomialRing<IntegerRing>>();
    }
}
