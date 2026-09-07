use std::marker::PhantomData;

use eqn_core::op::{Associative, BinaryOperator, Commutative};
use eqn_core::set::Set;

use super::{Group, NormalSubgroup, Subgroup};
use crate::group::AbelianGroup;
use crate::monoid::{Monoid, MonoidElem};

/// A left coset of `S`, represented by one element of the parent group.
/// Representatives `a` and `b` are equal when `a^-1 * b` belongs to `S`.
#[derive_where::derive_where(Clone, Debug, Eq)]
pub struct Coset<S: Subgroup> {
    representative: MonoidElem<S::Parent>,
    subgroup: PhantomData<S>,
}

impl<S: Subgroup> Coset<S> {
    pub const fn new(representative: MonoidElem<S::Parent>) -> Self {
        Self {
            representative,
            subgroup: PhantomData,
        }
    }

    pub const fn representative(&self) -> &MonoidElem<S::Parent> {
        &self.representative
    }

    pub fn into_representative(self) -> MonoidElem<S::Parent> {
        self.representative
    }

    pub fn applied(self, rhs: Self) -> Self {
        Self::new(S::Parent::apply(
            self.into_representative(),
            rhs.into_representative(),
        ))
    }

    pub fn inversed(self) -> Self {
        Self::new(S::Parent::inverse(self.into_representative()))
    }

    pub const fn identity() -> Self {
        Self::new(S::Parent::IDENTITY)
    }
}

impl<S: Subgroup> PartialEq for Coset<S> {
    fn eq(&self, other: &Self) -> bool {
        let displacement = S::Parent::apply(
            S::Parent::inverse(self.representative.clone()),
            other.representative.clone(),
        );
        S::contains(&displacement)
    }
}

/// The set of left cosets of `S`.
#[derive(Set)]
#[set(element = Coset<S>)]
pub struct Cosets<S: Subgroup>(PhantomData<S>);

/// Multiplication of cosets of a normal subgroup.
#[derive(Associative, BinaryOperator)]
#[operator(domain = Cosets<N>, apply = Coset::applied, identity = Coset::identity(), inverse = Coset::inversed)]
pub struct QuotientOp<N: NormalSubgroup>(PhantomData<N>);

impl<N: NormalSubgroup> Commutative for QuotientOp<N> where N::Parent: AbelianGroup {}

/// The quotient of a group by a normal subgroup.
pub type QuotientGroup<N> = (Cosets<N>, QuotientOp<N>);

#[cfg(test)]
mod tests {
    use eqn_core::set::Z;

    use super::*;
    use crate::group::AbelianGroup;
    use crate::monoid::Submonoid;
    use crate::operator_impl::ZAdd;

    type Integers = (Z, ZAdd);

    struct EvenIntegers;

    impl Submonoid for EvenIntegers {
        type Parent = Integers;

        fn contains(value: &MonoidElem<Self::Parent>) -> bool {
            value % 2 == 0
        }
    }

    impl Subgroup for EvenIntegers {}
    impl NormalSubgroup for EvenIntegers {}

    type IntegersModTwo = QuotientGroup<EvenIntegers>;

    fn modulo_two(value: i64) -> Coset<EvenIntegers> {
        Coset::new(value)
    }

    #[test]
    fn coset_equality_is_an_equivalence_relation() {
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
    fn quotient_of_an_abelian_group_is_abelian() {
        fn assert_group<G: Group>() {}
        fn assert_abelian<G: AbelianGroup>() {}

        assert_group::<IntegersModTwo>();
        assert_abelian::<IntegersModTwo>();
        assert_eq!(
            IntegersModTwo::apply(modulo_two(1), modulo_two(1)),
            IntegersModTwo::IDENTITY
        );
        assert_eq!(IntegersModTwo::inverse(modulo_two(1)), modulo_two(1));
    }

    #[test]
    fn quotient_operation_does_not_depend_on_representatives() {
        let product = IntegersModTwo::apply(modulo_two(1), modulo_two(2));
        let same_product = IntegersModTwo::apply(modulo_two(3), modulo_two(4));

        assert_eq!(product, same_product);
        assert_eq!(modulo_two(5).representative(), &5);
        assert_eq!(modulo_two(5).into_representative(), 5);
    }

    #[test]
    fn quotient_operator_satisfies_the_group_laws() {
        for a in -2..=2 {
            let value = modulo_two(a);
            let inverse = IntegersModTwo::inverse(value.clone());

            assert_eq!(
                IntegersModTwo::apply(value.clone(), IntegersModTwo::IDENTITY),
                value
            );
            assert_eq!(
                IntegersModTwo::apply(inverse, value.clone()),
                IntegersModTwo::IDENTITY
            );

            for b in -2..=2 {
                for c in -2..=2 {
                    assert_eq!(
                        IntegersModTwo::apply(
                            IntegersModTwo::apply(modulo_two(a), modulo_two(b)),
                            modulo_two(c)
                        ),
                        IntegersModTwo::apply(
                            modulo_two(a),
                            IntegersModTwo::apply(modulo_two(b), modulo_two(c))
                        )
                    );
                }
            }
        }
    }

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Symmetry {
        rotation: u8,
        reflected: bool,
    }

    impl Symmetry {
        const fn new(rotation: u8, reflected: bool) -> Self {
            Self {
                rotation,
                reflected,
            }
        }

        const fn applied(self, rhs: Self) -> Self {
            let rhs_rotation = if self.reflected {
                (3 - rhs.rotation) % 3
            } else {
                rhs.rotation
            };
            Symmetry::new(
                (self.rotation + rhs_rotation) % 3,
                self.reflected ^ rhs.reflected,
            )
        }

        const fn identity() -> Self {
            Self::new(0, false)
        }

        const fn inversed(self) -> Self {
            let rotation = if self.reflected {
                self.rotation
            } else {
                (3 - self.rotation) % 3
            };
            Self::new(rotation, self.reflected)
        }
    }

    #[derive(Set)]
    #[set(element = Symmetry)]
    struct TriangleSymmetries;

    #[derive(Associative, BinaryOperator)]
    #[operator(domain = TriangleSymmetries, apply = Symmetry::applied, identity = Symmetry::identity(), inverse = Symmetry::inversed)]
    struct Compose;

    type D3 = (TriangleSymmetries, Compose);

    struct Rotations;

    impl Submonoid for Rotations {
        type Parent = D3;

        fn contains(value: &MonoidElem<Self::Parent>) -> bool {
            !value.reflected
        }
    }

    impl Subgroup for Rotations {}
    impl NormalSubgroup for Rotations {}

    type D3ModuloRotations = QuotientGroup<Rotations>;

    fn symmetry(rotation: u8, reflected: bool) -> Symmetry {
        Symmetry::new(rotation, reflected)
    }

    fn symmetries() -> [Symmetry; 6] {
        [
            symmetry(0, false),
            symmetry(1, false),
            symmetry(2, false),
            symmetry(0, true),
            symmetry(1, true),
            symmetry(2, true),
        ]
    }

    fn modulo_rotations(rotation: u8, reflected: bool) -> Coset<Rotations> {
        Coset::new(symmetry(rotation, reflected))
    }

    #[test]
    fn triangle_symmetries_satisfy_the_group_laws() {
        for a in symmetries() {
            assert_eq!(D3::apply(a, D3::IDENTITY), a);
            assert_eq!(D3::apply(D3::IDENTITY, a), a);
            assert_eq!(D3::apply(D3::inverse(a), a), D3::IDENTITY);
            assert_eq!(D3::apply(a, D3::inverse(a)), D3::IDENTITY);

            for b in symmetries() {
                for c in symmetries() {
                    assert_eq!(D3::apply(D3::apply(a, b), c), D3::apply(a, D3::apply(b, c)));
                }
            }
        }
    }

    #[test]
    fn rotations_are_normal_in_the_triangle_symmetry_group() {
        let rotations = [symmetry(0, false), symmetry(1, false), symmetry(2, false)];

        for g in symmetries() {
            for n in rotations {
                let conjugate = D3::apply(D3::apply(g, n), D3::inverse(g));
                assert!(Rotations::contains(&conjugate));
            }
        }
    }

    #[test]
    fn quotient_of_a_noncommutative_group_is_well_defined() {
        fn assert_group<G: Group>() {}

        assert_group::<D3ModuloRotations>();
        assert_eq!(modulo_rotations(0, false), modulo_rotations(2, false));
        assert_eq!(modulo_rotations(0, true), modulo_rotations(2, true));
        assert_ne!(modulo_rotations(0, false), modulo_rotations(0, true));

        let product =
            D3ModuloRotations::apply(modulo_rotations(0, true), modulo_rotations(0, true));
        let same_product =
            D3ModuloRotations::apply(modulo_rotations(1, true), modulo_rotations(2, true));

        assert_eq!(product, D3ModuloRotations::IDENTITY);
        assert_eq!(product, same_product);
    }
}
