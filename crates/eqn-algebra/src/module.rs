use eqn_core::op::{Associative, BinaryOperator, Commutative, Identity, Inverse};
use eqn_core::set::{Set, Subset};

use crate::ring::{Ring, RingElem};

/// An element of a module.
pub type ModuleElem<M> = <M as Module>::Domain;

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

    fn scale(scalar: ModuleScalar<Self>, value: ModuleElem<Self>) -> ModuleElem<Self>;
}

/// A subset containing zero and closed under addition, additive inverses, and
/// scalar multiplication.
pub trait Submodule: Subset<Superset = <Self::Parent as Module>::Domain> {
    type Parent: Module;
}

#[cfg(test)]
mod tests {
    use eqn_core::set::Z;

    use super::*;
    use crate::operator_impl::{ZAdd, ZMul};
    use crate::ring::SemiRing;

    type Integers = (ZAdd, ZMul);

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

    impl Subset for EvenIntegers {
        type Superset = Z;

        fn contains(value: &Z) -> bool {
            i64::from(*value) % 2 == 0
        }
    }

    impl Submodule for EvenIntegers {
        type Parent = IntegerModule;
    }

    #[test]
    fn integer_module_exposes_its_structure_and_scalar_action() {
        type Addition = <IntegerModule as Module>::Addition;

        let scalar: ModuleScalar<IntegerModule> = Z::from(-3);
        let value: ModuleElem<IntegerModule> = Z::from(4);

        assert_eq!(Addition::identity(), Z::from(0));
        assert_eq!(Addition::apply(value, Z::from(5)), Z::from(9));
        assert_eq!(Addition::inverse(value), Z::from(-4));
        assert_eq!(IntegerModule::scale(scalar, value), Z::from(-12));
    }

    #[test]
    fn integers_satisfy_the_module_laws() {
        type Addition = <IntegerModule as Module>::Addition;

        let scalars = [-2, -1, 0, 1, 3].map(Z::from);
        let values = [-3, -1, 0, 2, 4].map(Z::from);

        for &r in &scalars {
            for &s in &scalars {
                for &x in &values {
                    assert_eq!(
                        IntegerModule::scale(Integers::add(r, s), x),
                        Addition::apply(IntegerModule::scale(r, x), IntegerModule::scale(s, x))
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
                        IntegerModule::scale(r, Addition::apply(x, y)),
                        Addition::apply(IntegerModule::scale(r, x), IntegerModule::scale(r, y))
                    );
                }

                assert_eq!(IntegerModule::scale(Integers::one(), x), x);
            }
        }
    }

    #[test]
    fn even_integers_form_a_submodule() {
        type Addition = <IntegerModule as Module>::Addition;

        fn assert_submodule<S: Submodule>() {}

        assert_submodule::<EvenIntegers>();
        assert!(EvenIntegers::contains(&Addition::identity()));

        for scalar in [-3, 0, 4].map(Z::from) {
            for value in [-8, -2, 0, 6].map(Z::from) {
                assert!(EvenIntegers::contains(&IntegerModule::scale(scalar, value)));
            }
        }
    }
}
