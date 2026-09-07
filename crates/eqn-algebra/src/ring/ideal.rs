use super::{Ring, RingElem, SemiRing};

/// A two-sided ideal of a ring.
///
/// Implementations must contain zero, be closed under subtraction, and absorb
/// multiplication from both sides by every element of the ring.
pub trait Ideal {
    type Ring: Ring;

    fn contains(value: &RingElem<Self::Ring>) -> bool;

    /// Whether this ideal is strictly smaller than its ring.
    fn is_proper() -> bool {
        !Self::contains(&Self::Ring::ONE)
    }
}

#[cfg(test)]
mod tests {
    use eqn_core::set::Z;

    use super::*;
    use crate::operator_impl::{ZAdd, ZMul};

    type Integers = (Z, ZAdd, ZMul);

    struct EvenIntegers;

    impl Ideal for EvenIntegers {
        type Ring = Integers;

        fn contains(value: &RingElem<Self::Ring>) -> bool {
            value % 2 == 0
        }
    }

    struct WholeRing;

    impl Ideal for WholeRing {
        type Ring = Integers;

        fn contains(_: &RingElem<Self::Ring>) -> bool {
            true
        }
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
