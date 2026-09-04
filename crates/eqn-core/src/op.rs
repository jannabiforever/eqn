pub use eqn_macros::{Associative, Commutative};

use crate::set::Set;

// ================================================================================
// Traits
// ================================================================================

pub trait BinaryOperator {
    type Domain: Set;
    fn apply(
        a: <Self::Domain as Set>::Element,
        b: <Self::Domain as Set>::Element,
    ) -> <Self::Domain as Set>::Element;
}

pub trait Associative: BinaryOperator {}

pub trait Commutative: BinaryOperator {}

pub trait Identity: BinaryOperator {
    const IDENTITY: <<Self as BinaryOperator>::Domain as Set>::Element;
}

pub trait Inverse: BinaryOperator {
    fn inverse(
        a: <<Self as BinaryOperator>::Domain as Set>::Element,
    ) -> <<Self as BinaryOperator>::Domain as Set>::Element;
}
