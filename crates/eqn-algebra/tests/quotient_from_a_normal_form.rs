use eqn_algebra::group::quotient::Modulo;
use eqn_algebra::operator_impl::{ZAdd, ZMul};
use eqn_algebra::ring::SemiRing;
use eqn_algebra::ring::ideal::Ideal;
use eqn_algebra::ring::quotient::QuotientRing;
use eqn_core::quotient::{Congruence, Equivalence, NormalForm, Quotient};
use eqn_core::set::Z;
use num_integer::Integer;

type Integers = (ZAdd, ZMul);

struct MultiplesOfSix;

impl NormalForm<Z> for MultiplesOfSix {
    fn reduce(element: Z) -> Z {
        element.mod_floor(&Z::from(6))
    }
}

impl Congruence<ZAdd> for MultiplesOfSix {}
impl Congruence<ZMul> for MultiplesOfSix {}

impl Ideal for MultiplesOfSix {
    type Ring = Integers;
}

type IntegersModSix = QuotientRing<MultiplesOfSix>;

fn class(value: i64) -> Quotient<Z, MultiplesOfSix> {
    Quotient::new(Z::from(value))
}

#[test]
fn reduction_mod_six_is_a_congruence_for_both_ring_operations() {
    for a in (-12..=12).map(Z::from) {
        for b in (-12..=12).map(Z::from) {
            let (a_reduced, b_reduced) = (
                MultiplesOfSix::reduce(a.clone()),
                MultiplesOfSix::reduce(b.clone()),
            );

            assert_eq!(
                MultiplesOfSix::reduce(Integers::add(a.clone(), b.clone())),
                MultiplesOfSix::reduce(Integers::add(a_reduced.clone(), b_reduced.clone()))
            );
            assert_eq!(
                MultiplesOfSix::reduce(Integers::multiply(a.clone(), b)),
                MultiplesOfSix::reduce(Integers::multiply(a_reduced, b_reduced))
            );
        }
    }
}

#[test]
fn residue_classes_add_and_multiply_as_integers_reduced_mod_six() {
    for a in 0..6 {
        for b in 0..6 {
            assert_eq!(
                IntegersModSix::add(class(a), class(b)).into_representative(),
                Z::from((a + b) % 6)
            );
            assert_eq!(
                IntegersModSix::multiply(class(a), class(b)).into_representative(),
                Z::from(a * b % 6)
            );
        }
    }
}

#[test]
fn two_and_three_are_zero_divisors_mod_six() {
    assert_ne!(class(2), IntegersModSix::zero());
    assert_ne!(class(3), IntegersModSix::zero());
    assert_eq!(
        IntegersModSix::multiply(class(2), class(3)),
        IntegersModSix::zero()
    );
}

#[test]
fn classes_are_equal_exactly_when_the_coset_relation_holds() {
    for a in -12..=12 {
        for b in -12..=12 {
            assert_eq!(
                class(a) == class(b),
                Modulo::<MultiplesOfSix>::equivalent(&Z::from(a), &Z::from(b))
            );
        }
    }
}
