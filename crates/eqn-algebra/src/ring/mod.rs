use std::collections::HashSet;
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

    fn degrees_of_freedom(&self) -> usize {
        let mut visited = HashSet::new();
        let mut to_visit = vec![self];
        while let Some(e) = to_visit.pop() {
            match e {
                SemiRingExpr::Const(_) => continue,
                SemiRingExpr::Symbol(symbol) => {
                    visited.insert(symbol);
                }
                SemiRingExpr::Add(semi_ring_exprs) => to_visit.extend(semi_ring_exprs.iter()),
                SemiRingExpr::Mul(semi_ring_exprs) => to_visit.extend(semi_ring_exprs.iter()),
                SemiRingExpr::Pow { base, .. } => to_visit.push(base),
            }
        }
        visited.len()
    }

    fn substitute(&mut self, sym: Symbol<Self::Domain>, expr: &Self) {
        let mut to_visit = vec![self];
        while let Some(e) = to_visit.pop() {
            match e {
                SemiRingExpr::Const(_) => continue,
                SemiRingExpr::Symbol(symbol) if *symbol == sym => *e = expr.clone(),
                SemiRingExpr::Symbol(_) => continue,
                SemiRingExpr::Add(semi_ring_exprs) => to_visit.extend(semi_ring_exprs.iter_mut()),
                SemiRingExpr::Mul(semi_ring_exprs) => to_visit.extend(semi_ring_exprs.iter_mut()),
                SemiRingExpr::Pow { base, .. } => to_visit.push(base),
            }
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

    fn degrees_of_freedom(&self) -> usize {
        let mut visited = HashSet::new();
        let mut to_visit = vec![self];
        while let Some(e) = to_visit.pop() {
            match e {
                RingExpr::Const(_) => continue,
                RingExpr::Symbol(symbol) => {
                    visited.insert(symbol);
                }
                RingExpr::Neg(e) => to_visit.push(e),
                RingExpr::Add(semi_ring_exprs) => to_visit.extend(semi_ring_exprs.iter()),
                RingExpr::Mul(semi_ring_exprs) => to_visit.extend(semi_ring_exprs.iter()),
                RingExpr::Pow { base, .. } => to_visit.push(base),
            }
        }
        visited.len()
    }

    fn substitute(&mut self, sym: Symbol<Self::Domain>, expr: &Self) {
        let mut to_visit = vec![self];
        while let Some(e) = to_visit.pop() {
            match e {
                RingExpr::Const(_) => continue,
                RingExpr::Symbol(symbol) if *symbol == sym => *e = expr.clone(),
                RingExpr::Symbol(_) => continue,
                RingExpr::Neg(e) => to_visit.push(e),
                RingExpr::Add(semi_ring_exprs) => to_visit.extend(semi_ring_exprs.iter_mut()),
                RingExpr::Mul(semi_ring_exprs) => to_visit.extend(semi_ring_exprs.iter_mut()),
                RingExpr::Pow { base, .. } => to_visit.push(base),
            }
        }
    }
}

impl<R: Ring> From<Symbol<R::Domain>> for RingExpr<R> {
    fn from(sym: Symbol<R::Domain>) -> Self {
        Self::Symbol(sym)
    }
}

mod rewriter;
pub use rewriter::{CommutativeRingRewriter, RingRewriter, SemiRingRewriter};
