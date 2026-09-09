use std::fmt;
use std::marker::PhantomData;

use eqn_core::op::{Associative, BinaryOperator, Commutative};
use eqn_core::set::Set;

use super::{CommutativeRing, Ideal, Ring, RingElem, SemiRing};

/// An equivalence class modulo `I`, represented by one element of the parent
/// ring. Representatives are equal when their difference belongs to `I`.
/// This equality relies on `I` satisfying the [`Ideal`] laws.
#[derive_where::derive_where(Clone)]
pub struct ResidueClass<I: Ideal> {
    representative: RingElem<I::Ring>,
    ideal: PhantomData<I>,
}

impl<I: Ideal> ResidueClass<I> {
    pub const fn new(representative: RingElem<I::Ring>) -> Self {
        Self {
            representative,
            ideal: PhantomData,
        }
    }

    pub const fn representative(&self) -> &RingElem<I::Ring> {
        &self.representative
    }

    pub fn into_representative(self) -> RingElem<I::Ring> {
        self.representative
    }

    pub fn added(self, rhs: Self) -> Self {
        ResidueClass::new(I::Ring::add(
            self.into_representative(),
            rhs.into_representative(),
        ))
    }

    pub fn multiplied(self, rhs: Self) -> Self {
        ResidueClass::new(I::Ring::multiply(
            self.into_representative(),
            rhs.into_representative(),
        ))
    }

    pub const fn zero() -> Self {
        ResidueClass::new(I::Ring::ZERO)
    }

    pub const fn one() -> Self {
        ResidueClass::new(I::Ring::ONE)
    }

    pub fn inversed(self) -> Self {
        ResidueClass::new(I::Ring::negate(self.into_representative()))
    }
}

impl<I: Ideal> fmt::Debug for ResidueClass<I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("ResidueClass")
            .field(&self.representative)
            .finish()
    }
}

impl<I: Ideal> PartialEq for ResidueClass<I> {
    fn eq(&self, other: &Self) -> bool {
        let difference = I::Ring::add(
            self.representative.clone(),
            I::Ring::negate(other.representative.clone()),
        );
        I::contains(&difference)
    }
}

impl<I: Ideal> Eq for ResidueClass<I> {}

/// The set of residue classes modulo `I`.
#[derive(Set)]
#[set(element = ResidueClass<I>)]
pub struct ResidueClasses<I: Ideal>(PhantomData<I>);

/// Addition of residue classes.
#[derive(Associative, BinaryOperator, Commutative)]
#[operator(
    domain = ResidueClasses<I>,
    symbol = <I::Ring as SemiRing>::ADD_SYMBOL,
    apply = ResidueClass::added,
    identity = ResidueClass::zero(),
    inverse = ResidueClass::inversed,
    inverse_symbol = <I::Ring as Ring>::SUB_SYMBOL
)]
pub struct QuotientAdd<I: Ideal>(PhantomData<I>);

/// Multiplication of residue classes.
#[derive(Associative, BinaryOperator)]
#[operator(
    domain = ResidueClasses<I>,
    symbol = <I::Ring as SemiRing>::MUL_SYMBOL,
    apply = ResidueClass::multiplied,
    identity = ResidueClass::one()
)]
pub struct QuotientMul<I: Ideal>(PhantomData<I>);

impl<I> Commutative for QuotientMul<I>
where
    I: Ideal,
    I::Ring: CommutativeRing,
{
}

/// The quotient of a ring by a two-sided ideal.
pub type QuotientRing<I> = (ResidueClasses<I>, QuotientAdd<I>, QuotientMul<I>);

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

    type IntegersModTwo = QuotientRing<EvenIntegers>;

    fn modulo_two(value: i64) -> ResidueClass<EvenIntegers> {
        ResidueClass::new(value)
    }

    #[test]
    fn equality_is_modulo_the_ideal() {
        assert_eq!(modulo_two(0), modulo_two(2));
        assert_eq!(modulo_two(1), modulo_two(3));
        assert_ne!(modulo_two(0), modulo_two(1));

        let value = modulo_two(5);
        assert_eq!(value.representative(), &5);
        assert_eq!(value.into_representative(), 5);
    }

    #[test]
    fn quotient_equality_is_an_equivalence_relation() {
        for a in -3..=3 {
            assert_eq!(modulo_two(a), modulo_two(a));

            for b in -3..=3 {
                assert_eq!(
                    modulo_two(a) == modulo_two(b),
                    modulo_two(b) == modulo_two(a)
                );

                for c in -3..=3 {
                    if modulo_two(a) == modulo_two(b) && modulo_two(b) == modulo_two(c) {
                        assert_eq!(modulo_two(a), modulo_two(c));
                    }
                }
            }
        }
    }

    #[test]
    fn quotient_operations_do_not_depend_on_representatives() {
        let sum = IntegersModTwo::add(modulo_two(1), modulo_two(2));
        let same_sum = IntegersModTwo::add(modulo_two(3), modulo_two(4));
        assert_eq!(sum, same_sum);

        let product = IntegersModTwo::multiply(modulo_two(1), modulo_two(2));
        let same_product = IntegersModTwo::multiply(modulo_two(3), modulo_two(4));
        assert_eq!(product, same_product);
    }

    #[test]
    fn integers_modulo_two_form_a_commutative_ring() {
        fn assert_ring<R: Ring>() {}
        fn assert_commutative_ring<R: CommutativeRing>() {}

        assert_ring::<IntegersModTwo>();
        assert_commutative_ring::<IntegersModTwo>();
        assert_eq!(
            IntegersModTwo::add(modulo_two(1), modulo_two(1)),
            modulo_two(0)
        );
        assert_eq!(
            IntegersModTwo::multiply(modulo_two(1), modulo_two(1)),
            modulo_two(1)
        );
        assert_eq!(IntegersModTwo::negate(modulo_two(1)), modulo_two(1));
    }

    #[test]
    fn quotient_operators_satisfy_the_ring_laws() {
        for a in -2..=2 {
            assert_eq!(
                IntegersModTwo::add(modulo_two(a), IntegersModTwo::ZERO),
                modulo_two(a)
            );
            assert_eq!(
                IntegersModTwo::add(modulo_two(a), IntegersModTwo::negate(modulo_two(a))),
                IntegersModTwo::ZERO
            );
            assert_eq!(
                IntegersModTwo::multiply(modulo_two(a), IntegersModTwo::ONE),
                modulo_two(a)
            );

            for b in -2..=2 {
                assert_eq!(
                    IntegersModTwo::add(modulo_two(a), modulo_two(b)),
                    IntegersModTwo::add(modulo_two(b), modulo_two(a))
                );
                assert_eq!(
                    IntegersModTwo::multiply(modulo_two(a), modulo_two(b)),
                    IntegersModTwo::multiply(modulo_two(b), modulo_two(a))
                );

                for c in -2..=2 {
                    assert_eq!(
                        IntegersModTwo::add(
                            IntegersModTwo::add(modulo_two(a), modulo_two(b)),
                            modulo_two(c)
                        ),
                        IntegersModTwo::add(
                            modulo_two(a),
                            IntegersModTwo::add(modulo_two(b), modulo_two(c))
                        )
                    );
                    assert_eq!(
                        IntegersModTwo::multiply(
                            IntegersModTwo::multiply(modulo_two(a), modulo_two(b)),
                            modulo_two(c)
                        ),
                        IntegersModTwo::multiply(
                            modulo_two(a),
                            IntegersModTwo::multiply(modulo_two(b), modulo_two(c))
                        )
                    );
                    assert_eq!(
                        IntegersModTwo::multiply(
                            modulo_two(a),
                            IntegersModTwo::add(modulo_two(b), modulo_two(c))
                        ),
                        IntegersModTwo::add(
                            IntegersModTwo::multiply(modulo_two(a), modulo_two(b)),
                            IntegersModTwo::multiply(modulo_two(a), modulo_two(c))
                        )
                    );
                    assert_eq!(
                        IntegersModTwo::multiply(
                            IntegersModTwo::add(modulo_two(a), modulo_two(b)),
                            modulo_two(c)
                        ),
                        IntegersModTwo::add(
                            IntegersModTwo::multiply(modulo_two(a), modulo_two(c)),
                            IntegersModTwo::multiply(modulo_two(b), modulo_two(c))
                        )
                    );
                }
            }
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
    fn quotient_by_the_whole_ring_is_the_zero_ring() {
        type ZeroRing = QuotientRing<WholeRing>;

        assert_eq!(ZeroRing::ZERO, ZeroRing::ONE);
    }

    struct ZeroIdeal;

    impl Ideal for ZeroIdeal {
        type Ring = Integers;

        fn contains(value: &RingElem<Self::Ring>) -> bool {
            *value == Integers::ZERO
        }
    }

    #[test]
    fn quotient_by_zero_preserves_equality() {
        for lhs in -3..=3 {
            for rhs in -3..=3 {
                assert_eq!(
                    ResidueClass::<ZeroIdeal>::new(lhs) == ResidueClass::new(rhs),
                    lhs == rhs
                );
            }
        }
    }
}
