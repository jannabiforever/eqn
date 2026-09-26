use std::marker::PhantomData;

use eqn_core::op::{Associative, BinaryOperator, Commutative};
use eqn_core::quotient::{NormalForm, Quotient};

use super::{CommutativeRing, RingElem, SemiRing};
use crate::group::quotient::{Modulo, QuotientOp};
use crate::ring::ideal::Ideal;

impl<I: Ideal + NormalForm<RingElem<I::Ring>>> Modulo<I> {
    /// `(a + I)(b + I) = ab + I`, well defined because `I` absorbs
    /// multiplication.
    pub fn multiplied(
        lhs: Quotient<RingElem<I::Ring>, I>,
        rhs: Quotient<RingElem<I::Ring>, I>,
    ) -> Quotient<RingElem<I::Ring>, I> {
        Quotient::new(I::Ring::multiply(
            lhs.into_representative(),
            rhs.into_representative(),
        ))
    }

    pub fn one() -> Quotient<RingElem<I::Ring>, I> {
        Quotient::new(I::Ring::one())
    }
}

/// Multiplication of residue classes.
#[derive(Associative, BinaryOperator)]
#[operator(domain = Quotient<RingElem<I::Ring>, I>, symbol = <I::Ring as SemiRing>::MUL_SYMBOL, apply = Modulo::<I>::multiplied, identity = Modulo::<I>::one())]
pub struct QuotientMul<I: Ideal + NormalForm<RingElem<I::Ring>>>(PhantomData<I>);

impl<I> Commutative for QuotientMul<I>
where
    I: Ideal + NormalForm<RingElem<I::Ring>>,
    I::Ring: CommutativeRing,
{
}

/// The quotient of a ring by a two-sided ideal. Its addition is the quotient
/// of the additive group.
pub type QuotientRing<I> = (QuotientOp<I>, QuotientMul<I>);

#[cfg(test)]
mod tests {
    use eqn_core::quotient::Equivalence;
    use eqn_core::set::{Subset, Z};
    use num_integer::Integer;

    use super::*;
    use crate::group::Subgroup;
    use crate::monoid::Submonoid;
    use crate::operator_impl::{ZAdd, ZMul};
    use crate::ring::Ring;

    type Integers = (ZAdd, ZMul);

    struct EvenIntegers;

    impl Subset for EvenIntegers {
        type Superset = Z;

        fn contains(value: &Z) -> bool {
            value % Z::from(2) == Z::ZERO
        }
    }

    impl Submonoid for EvenIntegers {
        type Parent = (ZAdd,);
    }

    impl Subgroup for EvenIntegers {}

    impl NormalForm<Z> for EvenIntegers {
        fn reduce(value: Z) -> Z {
            value.mod_floor(&Z::from(2))
        }
    }

    impl Ideal for EvenIntegers {
        type Ring = Integers;
    }

    type IntegersModTwo = QuotientRing<EvenIntegers>;

    fn modulo_two<V: Into<Z> + Clone>(value: &V) -> Quotient<Z, EvenIntegers> {
        Quotient::new(value.clone().into())
    }

    #[test]
    fn equality_is_modulo_the_ideal() {
        assert_eq!(modulo_two(&0), modulo_two(&2));
        assert_eq!(modulo_two(&1), modulo_two(&3));
        assert_ne!(modulo_two(&0), modulo_two(&1));

        let value = modulo_two(&5);
        assert_eq!(value.representative(), &Z::from(1));
        assert_eq!(value.into_representative(), Z::from(1));
    }

    #[test]
    fn quotient_equality_is_an_equivalence_relation() {
        for a in (-3..=3).map(Z::from) {
            assert_eq!(modulo_two(&a), modulo_two(&a));

            for b in (-3..=3).map(Z::from) {
                assert_eq!(
                    modulo_two(&a) == modulo_two(&b),
                    modulo_two(&b) == modulo_two(&a)
                );

                for c in -3..=3 {
                    if modulo_two(&a) == modulo_two(&b) && modulo_two(&b) == modulo_two(&c) {
                        assert_eq!(modulo_two(&a), modulo_two(&c));
                    }
                }
            }
        }
    }

    #[test]
    fn quotient_operations_do_not_depend_on_representatives() {
        let sum = IntegersModTwo::add(modulo_two(&1), modulo_two(&2));
        let same_sum = IntegersModTwo::add(modulo_two(&3), modulo_two(&4));
        assert_eq!(sum, same_sum);

        let product = IntegersModTwo::multiply(modulo_two(&1), modulo_two(&2));
        let same_product = IntegersModTwo::multiply(modulo_two(&3), modulo_two(&4));
        assert_eq!(product, same_product);
    }

    #[test]
    fn integers_modulo_two_add_to_zero_and_multiply_to_one() {
        assert_eq!(
            IntegersModTwo::add(modulo_two(&1), modulo_two(&1)),
            modulo_two(&0)
        );
        assert_eq!(
            IntegersModTwo::multiply(modulo_two(&1), modulo_two(&1)),
            modulo_two(&1)
        );
        assert_eq!(IntegersModTwo::negate(modulo_two(&1)), modulo_two(&1));
    }

    #[test]
    fn quotient_operators_satisfy_the_ring_laws() {
        for a in (-2..=2).map(Z::from) {
            assert_eq!(
                IntegersModTwo::add(modulo_two(&a), IntegersModTwo::zero()),
                modulo_two(&a)
            );
            assert_eq!(
                IntegersModTwo::add(modulo_two(&a), IntegersModTwo::negate(modulo_two(&a))),
                IntegersModTwo::zero()
            );
            assert_eq!(
                IntegersModTwo::multiply(modulo_two(&a), IntegersModTwo::one()),
                modulo_two(&a)
            );

            for b in (-2..=2).map(Z::from) {
                assert_eq!(
                    IntegersModTwo::add(modulo_two(&a), modulo_two(&b)),
                    IntegersModTwo::add(modulo_two(&b), modulo_two(&a))
                );
                assert_eq!(
                    IntegersModTwo::multiply(modulo_two(&a), modulo_two(&b)),
                    IntegersModTwo::multiply(modulo_two(&b), modulo_two(&a))
                );

                for c in -2..=2 {
                    assert_eq!(
                        IntegersModTwo::add(
                            IntegersModTwo::add(modulo_two(&a), modulo_two(&b)),
                            modulo_two(&c)
                        ),
                        IntegersModTwo::add(
                            modulo_two(&a),
                            IntegersModTwo::add(modulo_two(&b), modulo_two(&c))
                        )
                    );
                    assert_eq!(
                        IntegersModTwo::multiply(
                            IntegersModTwo::multiply(modulo_two(&a), modulo_two(&b)),
                            modulo_two(&c)
                        ),
                        IntegersModTwo::multiply(
                            modulo_two(&a),
                            IntegersModTwo::multiply(modulo_two(&b), modulo_two(&c))
                        )
                    );
                    assert_eq!(
                        IntegersModTwo::multiply(
                            modulo_two(&a),
                            IntegersModTwo::add(modulo_two(&b), modulo_two(&c))
                        ),
                        IntegersModTwo::add(
                            IntegersModTwo::multiply(modulo_two(&a), modulo_two(&b)),
                            IntegersModTwo::multiply(modulo_two(&a), modulo_two(&c))
                        )
                    );
                    assert_eq!(
                        IntegersModTwo::multiply(
                            IntegersModTwo::add(modulo_two(&a), modulo_two(&b)),
                            modulo_two(&c)
                        ),
                        IntegersModTwo::add(
                            IntegersModTwo::multiply(modulo_two(&a), modulo_two(&c)),
                            IntegersModTwo::multiply(modulo_two(&b), modulo_two(&c))
                        )
                    );
                }
            }
        }
    }

    struct WholeRing;

    impl Subset for WholeRing {
        type Superset = Z;

        fn contains(_: &Z) -> bool {
            true
        }
    }

    impl Submonoid for WholeRing {
        type Parent = (ZAdd,);
    }

    impl Subgroup for WholeRing {}

    impl NormalForm<Z> for WholeRing {
        fn reduce(_: Z) -> Z {
            Z::ZERO
        }
    }

    impl Ideal for WholeRing {
        type Ring = Integers;
    }

    #[test]
    fn residue_classes_agree_with_the_ideal() {
        for a in (-3..=3).map(Z::from) {
            for b in (-3..=3).map(Z::from) {
                assert_eq!(
                    modulo_two(&a) == modulo_two(&b),
                    Modulo::<EvenIntegers>::equivalent(&Z::from(a.clone()), &Z::from(b.clone()))
                );
                assert_eq!(
                    Quotient::<Z, WholeRing>::new(a.clone()) == Quotient::new(b.clone()),
                    Modulo::<WholeRing>::equivalent(&a, &b)
                );
                assert_eq!(
                    Quotient::<Z, ZeroIdeal>::new(a.clone()) == Quotient::new(b.clone()),
                    Modulo::<ZeroIdeal>::equivalent(&a, &b)
                );
            }
        }
    }

    #[test]
    fn quotient_by_the_whole_ring_is_the_zero_ring() {
        type ZeroRing = QuotientRing<WholeRing>;

        assert_eq!(ZeroRing::zero(), ZeroRing::one());
    }

    struct ZeroIdeal;

    impl Subset for ZeroIdeal {
        type Superset = Z;

        fn contains(value: &Z) -> bool {
            *value == Integers::zero()
        }
    }

    impl Submonoid for ZeroIdeal {
        type Parent = (ZAdd,);
    }

    impl Subgroup for ZeroIdeal {}

    impl NormalForm<Z> for ZeroIdeal {
        fn reduce(value: Z) -> Z {
            value
        }
    }

    impl Ideal for ZeroIdeal {
        type Ring = Integers;
    }

    #[test]
    fn quotient_by_zero_preserves_equality() {
        for lhs in (-3..=3).map(Z::from) {
            for rhs in (-3..=3).map(Z::from) {
                assert_eq!(
                    Quotient::<Z, ZeroIdeal>::new(lhs.clone()) == Quotient::new(rhs.clone()),
                    lhs == rhs
                );
            }
        }
    }
}
