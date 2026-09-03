use crate::monoid::Monoid;
use crate::op::{BinaryOperator, CommutativeOperator, InverseOperator};
use crate::set::Set;

/// A group: a set equipped with an associative binary operation, an identity
/// element, and a two-sided inverse for every element.
///
/// The inherited [`Monoid`] supplies the set, operation, and identity.
/// [`InverseOperator`] declares that, for every element `x`, both
/// `inverse(x) * x` and `x * inverse(x)` equal [`Monoid::IDENTITY`], where `*`
/// denotes [`Monoid::apply`]. Rust cannot verify these laws, so implementations
/// should cover them with property tests where practical.
pub trait Group: Monoid<Operator: BinaryOperator + InverseOperator> {
    /// Returns the two-sided inverse of `value` under the group's operation.
    fn inverse(value: <Self::Domain as Set>::Element) -> <Self::Domain as Set>::Element {
        <Self::Operator as InverseOperator>::inverse(value)
    }
}

/// Classifies every monoid whose operation supplies inverses as a group.
impl<M> Group for M
where
    M: Monoid,
    M::Operator: InverseOperator,
{
}

/// An abelian group: a group whose operation is commutative.
///
/// In addition to the group laws, `x * y` must equal `y * x` for every pair of
/// elements in the set. [`CommutativeOperator`] declares this law.
pub trait AbelianGroup: Group + Monoid<Operator: CommutativeOperator> {}

/// Classifies every group with a commutative operation as an abelian group.
impl<G> AbelianGroup for G
where
    G: Group,
    G::Operator: CommutativeOperator,
{
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::op::{AssociativeOperator, BinaryOperator, IdentityOperator};

    struct IntegerSet;

    impl Set for IntegerSet {
        type Element = i64;
    }

    struct Addition;

    impl BinaryOperator for Addition {
        type Domain = IntegerSet;

        fn apply(a: i64, b: i64) -> i64 {
            a + b
        }
    }

    impl AssociativeOperator for Addition {}

    impl CommutativeOperator for Addition {}

    impl IdentityOperator for Addition {
        const IDENTITY: i64 = 0;
    }

    impl InverseOperator for Addition {
        fn inverse(a: i64) -> i64 {
            -a
        }
    }

    type IntegerAdditionGroup = (IntegerSet, Addition);

    #[test]
    fn invertible_monoid_is_a_group() {
        assert_eq!(IntegerAdditionGroup::inverse(7), -7);
    }

    #[test]
    fn inverse_satisfies_both_group_laws() {
        for value in [-10, -1, 0, 1, 10] {
            let inverse = IntegerAdditionGroup::inverse(value);

            assert_eq!(
                IntegerAdditionGroup::apply(inverse, value),
                IntegerAdditionGroup::IDENTITY
            );
            assert_eq!(
                IntegerAdditionGroup::apply(value, inverse),
                IntegerAdditionGroup::IDENTITY
            );
        }
    }

    #[test]
    fn abelian_group_operator_is_commutative() {
        for lhs in [-10, -1, 0, 1, 10] {
            for rhs in [-10, -1, 0, 1, 10] {
                assert_eq!(
                    IntegerAdditionGroup::apply(lhs, rhs),
                    IntegerAdditionGroup::apply(rhs, lhs)
                );
            }
        }
    }
}
