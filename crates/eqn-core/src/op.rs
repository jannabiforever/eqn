pub use eqn_macros::{Associative, BinaryOperator, Commutative};

use crate::set::Set;

// ================================================================================
// Traits
// ================================================================================

/// Represents a binary operation over a given domain.
pub trait BinaryOperator {
    type Domain: Set;

    /// How the operator is spelled in source text: `a SYMBOL b`.
    const SYMBOL: &'static str;

    fn apply(
        a: <Self::Domain as Set>::Element,
        b: <Self::Domain as Set>::Element,
    ) -> <Self::Domain as Set>::Element;
}

/// Alias for a [`BinaryOperator`]'s Domain
pub type BinaryOperatorDomain<B> = <B as BinaryOperator>::Domain;

/// Alias for a [`BinaryOperator`]'s Domain Element
pub type BinaryOperatorDomainElement<B> = <BinaryOperatorDomain<B> as Set>::Element;

/// Marks a binary operation as associative:
///
/// `Op(Op(a, b), c) == Op(a, Op(b, c))` for all `a`, `b`, `c` in the domain.
pub trait Associative: BinaryOperator {}

/// Marks a binary operation as commutative:
///
/// `Op(a, b) == Op(b, a)` for all `a`, `b` in the domain.
pub trait Commutative: BinaryOperator {}

/// Marks a binary operation as having an identity element in the domain.
///
/// There exists an element `IDENTITY` such that for all `a` in the domain,
/// `Op(a, IDENTITY) == Op(IDENTITY, a) == a`.
pub trait Identity: BinaryOperator {
    const IDENTITY: BinaryOperatorDomainElement<Self>;
}

/// Marks a binary operation as having an inverse for every element in the
/// domain.
///
/// For all `a` in the domain, `inverse(a)` denotes the inverse element of `a`
/// with respect to `Op`.
pub trait Inverse: Identity {
    /// How "apply to the inverse" is spelled: `a INVERSE_SYMBOL b` is
    /// `Op(a, inverse(b))`, and `INVERSE_SYMBOL a` is `inverse(a)`.
    const INVERSE_SYMBOL: &'static str;

    fn inverse(a: BinaryOperatorDomainElement<Self>) -> BinaryOperatorDomainElement<Self>;
}
