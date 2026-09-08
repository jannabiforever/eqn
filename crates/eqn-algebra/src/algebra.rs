use crate::module::{Module, ModuleScalar};
use crate::ring::{CommutativeRing, Ring, RingElem, SemiRing, Subring};

/// An associative unital algebra over a commutative ring.
///
/// The module and ring additions are the same. Scalar multiplication is
/// compatible with multiplication in the algebra and acts centrally.
pub trait Algebra:
    Ring
    + Module<
        Scalars: CommutativeRing,
        Domain = <Self as SemiRing>::Domain,
        Addition = <Self as SemiRing>::Addition,
    >
{
    fn from_scalar(scalar: ModuleScalar<Self>) -> RingElem<Self> {
        Self::scale(scalar, Self::ONE)
    }
}

impl<A> Algebra for A
where
    A: Ring + Module<Domain = <A as SemiRing>::Domain, Addition = <A as SemiRing>::Addition>,
    A::Scalars: CommutativeRing,
{
}

/// A unital subring closed under scalar multiplication.
pub trait Subalgebra: Subring<Parent: Algebra> {}

#[cfg(test)]
mod tests {
    use eqn_core::set::Z;

    use super::*;
    use crate::module::ModuleElem;
    use crate::operator_impl::{ZAdd, ZMul};
    use crate::ring::SubSemiRing;

    type Integers = (Z, ZAdd, ZMul);

    struct IntegerAlgebra;

    impl SemiRing for IntegerAlgebra {
        type Domain = Z;
        type Addition = ZAdd;
        type Multiplication = ZMul;
    }

    impl Module for IntegerAlgebra {
        type Scalars = Integers;
        type Domain = Z;
        type Addition = ZAdd;

        fn scale(scalar: ModuleScalar<Self>, value: ModuleElem<Self>) -> ModuleElem<Self> {
            Integers::multiply(scalar, value)
        }
    }

    struct AllIntegers;

    impl SubSemiRing for AllIntegers {
        type Parent = IntegerAlgebra;

        fn contains(_: &RingElem<Self::Parent>) -> bool {
            true
        }
    }

    impl Subring for AllIntegers {}

    impl Subalgebra for AllIntegers {}

    #[test]
    fn compatible_ring_and_module_form_an_algebra() {
        fn assert_algebra<A: Algebra>() {}

        assert_algebra::<IntegerAlgebra>();
        assert_eq!(IntegerAlgebra::from_scalar(7), 7);
    }

    #[test]
    fn compatible_substructures_form_a_subalgebra() {
        fn assert_subalgebra<S: Subalgebra>() {}

        assert_subalgebra::<AllIntegers>();
    }
}
