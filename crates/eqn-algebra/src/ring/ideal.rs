use super::{Ring, RingAdd, RingElem, SemiRing};
use crate::group::normal::NormalSubgroup;
use crate::monoid::Monoid;

/// A two-sided ideal of a ring: a normal subgroup of the additive group that
/// absorbs multiplication from both sides by every element of the ring.
pub trait Ideal:
    NormalSubgroup<Parent: Monoid<Domain = RingElem<Self::Ring>, Operator = RingAdd<Self::Ring>>>
{
    type Ring: Ring;

    /// Whether this ideal is strictly smaller than its ring.
    fn is_proper() -> bool {
        !Self::contains(&Self::Ring::ONE)
    }
}

#[cfg(test)]
mod tests {
    use eqn_core::set::{Subset, Z};

    use super::*;
    use crate::group::Subgroup;
    use crate::monoid::Submonoid;
    use crate::operator_impl::{ZAdd, ZMul};

    type Integers = (ZAdd, ZMul);

    struct EvenIntegers;

    impl Subset for EvenIntegers {
        type Superset = Z;

        fn contains(value: &i64) -> bool {
            value % 2 == 0
        }
    }

    impl Submonoid for EvenIntegers {
        type Parent = (ZAdd,);
    }

    impl Subgroup for EvenIntegers {}

    impl Ideal for EvenIntegers {
        type Ring = Integers;
    }

    struct WholeRing;

    impl Subset for WholeRing {
        type Superset = Z;

        fn contains(_: &i64) -> bool {
            true
        }
    }

    impl Submonoid for WholeRing {
        type Parent = (ZAdd,);
    }

    impl Subgroup for WholeRing {}

    impl Ideal for WholeRing {
        type Ring = Integers;
    }

    #[test]
    fn membership_and_properness() {
        assert!(EvenIntegers::contains(&0));
        assert!(EvenIntegers::contains(&6));
        assert!(!EvenIntegers::contains(&3));
        assert!(EvenIntegers::is_proper());
        assert!(!WholeRing::is_proper());
    }

    #[test]
    fn even_integers_satisfy_the_ideal_laws() {
        let ideal_elements = [-6, -2, 0, 4, 8];
        let ring_elements = [-3, -1, 0, 2, 5];

        for &lhs in &ideal_elements {
            for &rhs in &ideal_elements {
                assert!(EvenIntegers::contains(&Integers::add(
                    lhs,
                    Integers::negate(rhs)
                )));
            }

            for &ring_element in &ring_elements {
                assert!(EvenIntegers::contains(&Integers::multiply(
                    ring_element,
                    lhs
                )));
                assert!(EvenIntegers::contains(&Integers::multiply(
                    lhs,
                    ring_element
                )));
            }
        }
    }
}
