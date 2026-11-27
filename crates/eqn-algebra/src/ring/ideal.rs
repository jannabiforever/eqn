use eqn_core::quotient::Congruence;

use super::{CommutativeRing, Ring, RingAdd, RingElem, RingMul, SemiRing};
use crate::group::normal::NormalSubgroup;

/// A two-sided ideal `I` of a ring, presented by a normal form for its
/// residue classes.
///
/// The normal form is declared a congruence for both ring operations. The
/// class of zero is then a two-sided ideal and the classes are its cosets
/// `a + I`, so membership in `I` is derived from the normal form.
pub trait Ideal: Congruence<RingAdd<Self::Ring>> + Congruence<RingMul<Self::Ring>> {
    type Ring: Ring;

    /// Whether `I` is strictly smaller than its ring.
    fn is_proper() -> bool {
        !<Self as NormalSubgroup>::contains(&Self::Ring::one())
    }
}

/// An ideal is a normal subgroup of the additive group of its ring.
impl<I: Ideal + ?Sized> NormalSubgroup for I {
    type Group = (RingAdd<I::Ring>,);
}

/// A maximal ideal `I` of a commutative ring: `I` is proper and no ideal lies
/// strictly between `I` and the ring, so the quotient by `I` is a field.
///
/// For `a` outside `I`, `inverse(a)` is an element `b` with `ab - 1` in `I`.
/// No such `b` exists for `a` in `I`, and asking for one is a contract
/// violation.
pub trait MaximalIdeal: Ideal<Ring: CommutativeRing> {
    fn inverse(element: RingElem<Self::Ring>) -> RingElem<Self::Ring>;
}

#[cfg(test)]
mod tests {
    use eqn_core::quotient::NormalForm;
    use eqn_core::set::Z;
    use num_integer::Integer;

    use super::*;
    use crate::operator_impl::{ZAdd, ZMul};

    type Integers = (ZAdd, ZMul);

    struct EvenIntegers;

    impl NormalForm<Z> for EvenIntegers {
        fn reduce(value: Z) -> Z {
            value.mod_floor(&Z::from(2))
        }
    }

    impl Congruence<ZAdd> for EvenIntegers {}
    impl Congruence<ZMul> for EvenIntegers {}

    impl Ideal for EvenIntegers {
        type Ring = Integers;
    }

    struct WholeRing;

    impl NormalForm<Z> for WholeRing {
        fn reduce(_: Z) -> Z {
            Z::ZERO
        }
    }

    impl Congruence<ZAdd> for WholeRing {}
    impl Congruence<ZMul> for WholeRing {}

    impl Ideal for WholeRing {
        type Ring = Integers;
    }

    #[test]
    fn membership_and_properness() {
        assert!(EvenIntegers::contains(&Z::from(6)));
        assert!(!EvenIntegers::contains(&Z::from(3)));
        assert!(EvenIntegers::is_proper());
        assert!(!WholeRing::is_proper());
    }

    #[test]
    fn even_integers_satisfy_the_ideal_laws() {
        let ideal_elements = [-6, -2, 0, 4, 8].map(Z::from);
        let ring_elements = [-3, -1, 0, 2, 5].map(Z::from);

        for lhs in &ideal_elements {
            for rhs in &ideal_elements {
                assert!(EvenIntegers::contains(&Integers::add(
                    lhs.clone(),
                    Integers::negate(rhs.clone())
                )));
            }

            for ring_element in &ring_elements {
                assert!(EvenIntegers::contains(&Integers::multiply(
                    ring_element.clone(),
                    lhs.clone()
                )));
                assert!(EvenIntegers::contains(&Integers::multiply(
                    lhs.clone(),
                    ring_element.clone()
                )));
            }
        }
    }

    #[test]
    fn reduction_mod_two_is_a_congruence_for_both_ring_operations() {
        for a in (-5..=5).map(Z::from) {
            for b in (-5..=5).map(Z::from) {
                let (a_reduced, b_reduced) = (
                    EvenIntegers::reduce(a.clone()),
                    EvenIntegers::reduce(b.clone()),
                );

                assert_eq!(
                    EvenIntegers::reduce(Integers::add(a.clone(), b.clone())),
                    EvenIntegers::reduce(Integers::add(a_reduced.clone(), b_reduced.clone()))
                );
                assert_eq!(
                    EvenIntegers::reduce(Integers::multiply(a.clone(), b)),
                    EvenIntegers::reduce(Integers::multiply(a_reduced, b_reduced))
                );
            }
        }
    }

    #[test]
    fn reduction_to_zero_is_a_congruence_for_both_ring_operations() {
        for a in (-5..=5).map(Z::from) {
            for b in (-5..=5).map(Z::from) {
                let (a_reduced, b_reduced) =
                    (WholeRing::reduce(a.clone()), WholeRing::reduce(b.clone()));

                assert_eq!(
                    WholeRing::reduce(Integers::add(a.clone(), b.clone())),
                    WholeRing::reduce(Integers::add(a_reduced.clone(), b_reduced.clone()))
                );
                assert_eq!(
                    WholeRing::reduce(Integers::multiply(a.clone(), b)),
                    WholeRing::reduce(Integers::multiply(a_reduced, b_reduced))
                );
            }
        }
    }
}
