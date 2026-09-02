use crate::domain::Domain;
use crate::monoid::Monoid;
use crate::op::{CommutativeOperator, InverseOperator};

/// A monoid in which every element has a (two-sided) inverse.
///
/// Implementing [`InverseOperator`] is a declaration that, for every element
/// `x`, both `inverse(x) * x` and `x * inverse(x)` equal [`Monoid::IDENTITY`],
/// where `*` denotes [`Monoid::apply`]. TODO: Rust cannot verify these laws, so
/// implementations should cover them with property tests where practical.
pub trait Group: Monoid<Operator: InverseOperator<Self::Domain>> {
    /// Returns the inverse of `value` under this group's operator.
    fn inverse(value: <Self::Domain as Domain>::Element) -> <Self::Domain as Domain>::Element {
        <Self::Operator as InverseOperator<Self::Domain>>::inverse(value)
    }
}

/// Every monoid whose operator supplies inverses forms a group.
impl<M> Group for M
where
    M: Monoid,
    M::Operator: InverseOperator<M::Domain>,
{
}

/// A group whose operator is commutative.
///
/// In addition to the group laws, the [`CommutativeOperator`] is needed.
pub trait AbelianGroup: Group + Monoid<Operator: CommutativeOperator<Self::Domain>> {}

/// Every group with a commutative operator forms an abelian group.
impl<G> AbelianGroup for G
where
    G: Group,
    G::Operator: CommutativeOperator<G::Domain>,
{
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::op::{AssociativeOperator, BinaryOperator, IdentityOperator};

    struct Integer;

    impl Domain for Integer {
        type Element = i64;
    }

    struct Addition;

    impl BinaryOperator<Integer> for Addition {
        fn apply(a: i64, b: i64) -> i64 {
            a + b
        }
    }

    impl AssociativeOperator<Integer> for Addition {}

    impl CommutativeOperator<Integer> for Addition {}

    impl IdentityOperator<Integer> for Addition {
        const IDENTITY: i64 = 0;
    }

    impl InverseOperator<Integer> for Addition {
        fn inverse(a: i64) -> i64 {
            -a
        }
    }

    type IntegerAddition = (Integer, Addition);

    #[test]
    fn invertible_monoid_is_a_group() {
        fn assert_group<G: Group>() {}

        assert_group::<IntegerAddition>();
        assert_eq!(IntegerAddition::inverse(7), -7);
    }

    #[test]
    fn inverse_satisfies_both_group_laws() {
        for value in [-10, -1, 0, 1, 10] {
            let inverse = IntegerAddition::inverse(value);

            assert_eq!(
                IntegerAddition::apply(inverse, value),
                IntegerAddition::IDENTITY
            );
            assert_eq!(
                IntegerAddition::apply(value, inverse),
                IntegerAddition::IDENTITY
            );
        }
    }

    #[test]
    fn commutative_group_is_an_abelian_group() {
        fn assert_commutative_operator<D, Op>()
        where
            D: Domain,
            Op: CommutativeOperator<D>,
        {
        }

        fn assert_abelian_group<G: AbelianGroup>() {
            assert_commutative_operator::<G::Domain, G::Operator>();
        }

        assert_abelian_group::<IntegerAddition>();
    }

    #[test]
    fn abelian_group_operator_is_commutative() {
        for lhs in [-10, -1, 0, 1, 10] {
            for rhs in [-10, -1, 0, 1, 10] {
                assert_eq!(
                    IntegerAddition::apply(lhs, rhs),
                    IntegerAddition::apply(rhs, lhs)
                );
            }
        }
    }
}
