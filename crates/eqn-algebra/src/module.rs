use crate::op::{Associative, BinaryOperator, Commutative, Identity, Inverse};
use crate::ring::{Ring, RingElem};
use crate::set::{Elem, Set};

/// An element of a module.
pub type ModuleElem<M> = Elem<<M as Module>::Domain>;

/// A scalar of a module.
pub type ModuleScalar<M> = RingElem<<M as Module>::Scalars>;

/// A left module over a ring.
///
/// Addition makes the domain an abelian group. Scalar multiplication is
/// unital, distributes over both additions, and respects scalar
/// multiplication.
pub trait Module {
    type Scalars: Ring;
    type Domain: Set;
    type Addition: BinaryOperator<Domain = Self::Domain>
        + Associative
        + Commutative
        + Identity
        + Inverse;

    const ZERO: ModuleElem<Self> = <Self::Addition as Identity>::IDENTITY;

    fn add(lhs: ModuleElem<Self>, rhs: ModuleElem<Self>) -> ModuleElem<Self> {
        <Self::Addition as BinaryOperator>::apply(lhs, rhs)
    }

    fn negate(value: ModuleElem<Self>) -> ModuleElem<Self> {
        <Self::Addition as Inverse>::inverse(value)
    }

    fn scale(scalar: ModuleScalar<Self>, value: ModuleElem<Self>) -> ModuleElem<Self>;
}

/// A subset containing zero and closed under addition, additive inverses, and
/// scalar multiplication.
pub trait Submodule {
    type Parent: Module;

    fn contains(value: &ModuleElem<Self::Parent>) -> bool;
}

#[cfg(test)]
mod tests {
    use eqn_core::set::Z;

    use super::*;
    use crate::operator_impl::{ZAdd, ZMul};
    use crate::ring::SemiRing;

    type Integers = (Z, ZAdd, ZMul);

    struct IntegerModule;

    impl Module for IntegerModule {
        type Scalars = Integers;
        type Domain = Z;
        type Addition = ZAdd;

        fn scale(scalar: ModuleScalar<Self>, value: ModuleElem<Self>) -> ModuleElem<Self> {
            Integers::multiply(scalar, value)
        }
    }

    struct EvenIntegers;

    impl Submodule for EvenIntegers {
        type Parent = IntegerModule;

        fn contains(value: &ModuleElem<Self::Parent>) -> bool {
            value % 2 == 0
        }
    }

    #[test]
    fn integer_module_helpers_use_the_additive_structure() {
        let scalar: ModuleScalar<IntegerModule> = -3;
        let value: ModuleElem<IntegerModule> = 4;

        assert_eq!(IntegerModule::ZERO, 0);
        assert_eq!(IntegerModule::add(value, 5), 9);
        assert_eq!(IntegerModule::negate(value), -4);
        assert_eq!(IntegerModule::scale(scalar, value), -12);
    }

    #[test]
    fn integers_satisfy_the_module_laws() {
        let scalars = [-2, -1, 0, 1, 3];
        let values = [-3, -1, 0, 2, 4];

        for &r in &scalars {
            for &s in &scalars {
                for &x in &values {
                    assert_eq!(
                        IntegerModule::scale(Integers::add(r, s), x),
                        IntegerModule::add(IntegerModule::scale(r, x), IntegerModule::scale(s, x))
                    );
                    assert_eq!(
                        IntegerModule::scale(Integers::multiply(r, s), x),
                        IntegerModule::scale(r, IntegerModule::scale(s, x))
                    );
                }
            }

            for &x in &values {
                for &y in &values {
                    assert_eq!(
                        IntegerModule::scale(r, IntegerModule::add(x, y)),
                        IntegerModule::add(IntegerModule::scale(r, x), IntegerModule::scale(r, y))
                    );
                }

                assert_eq!(IntegerModule::scale(Integers::ONE, x), x);
            }
        }
    }

    #[test]
    fn even_integers_form_a_submodule() {
        fn assert_submodule<S: Submodule>() {}

        assert_submodule::<EvenIntegers>();
        assert!(EvenIntegers::contains(&IntegerModule::ZERO));

        for scalar in [-3, 0, 4] {
            for value in [-8, -2, 0, 6] {
                assert!(EvenIntegers::contains(&IntegerModule::scale(scalar, value)));
            }
        }
    }
}
