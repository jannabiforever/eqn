use std::marker::PhantomData;

use eqn_core::op::{Associative, BinaryOperator, Commutative};
use eqn_core::quotient::{Equivalence, NormalForm, Quotient};

use crate::group::normal::NormalSubgroup;
use crate::group::{AbelianGroup, Group, Subgroup};
use crate::monoid::{Monoid, MonoidElem, Submonoid};

/// The domain of the parent group of `S`.
type Dom<S> = <<S as Submonoid>::Parent as Monoid>::Domain;

/// The left-coset relation of `S`: `a` and `b` are related when `a^-1 * b`
/// belongs to `S`. A normal form for the cosets of `S` must agree with it.
pub struct Modulo<S: Subgroup>(PhantomData<S>);

impl<S: Subgroup> Equivalence<Dom<S>> for Modulo<S> {
    fn equivalent(a: &MonoidElem<S::Parent>, b: &MonoidElem<S::Parent>) -> bool {
        S::contains(&S::Parent::apply(S::Parent::inverse(a.clone()), b.clone()))
    }
}

impl<N: NormalSubgroup + NormalForm<Dom<N>>> Modulo<N> {
    /// `(aN)(bN) = (ab)N`, well defined because `N` is normal.
    pub fn applied(lhs: Quotient<Dom<N>, N>, rhs: Quotient<Dom<N>, N>) -> Quotient<Dom<N>, N> {
        Quotient::new(N::Parent::apply(
            lhs.into_representative(),
            rhs.into_representative(),
        ))
    }

    pub fn inversed(coset: Quotient<Dom<N>, N>) -> Quotient<Dom<N>, N> {
        Quotient::new(N::Parent::inverse(coset.into_representative()))
    }

    pub fn identity() -> Quotient<Dom<N>, N> {
        Quotient::new(N::Parent::identity())
    }
}

/// Multiplication of cosets of a normal subgroup.
#[derive(Associative, BinaryOperator)]
#[operator(domain = Quotient<Dom<N>, N>, symbol = <N::Parent as Monoid>::SYMBOL, apply = Modulo::<N>::applied, identity = Modulo::<N>::identity(), inverse = Modulo::<N>::inversed, inverse_symbol = <N::Parent as Group>::INVERSE_SYMBOL)]
pub struct QuotientOp<N: NormalSubgroup + NormalForm<Dom<N>>>(PhantomData<N>);

impl<N: NormalSubgroup + NormalForm<Dom<N>>> Commutative for QuotientOp<N> where
    N::Parent: AbelianGroup
{
}

/// The quotient of a group by a normal subgroup, on the representatives `N`
/// chooses.
pub type QuotientGroup<N> = (QuotientOp<N>,);

#[cfg(test)]
mod tests {
    use eqn_core::set::{Set, Subset, Z};
    use num_integer::Integer;

    use super::*;
    use crate::operator_impl::ZAdd;

    type Integers = (ZAdd,);

    struct EvenIntegers;

    impl Subset for EvenIntegers {
        type Superset = Z;

        fn contains(value: &Z) -> bool {
            value % Z::from(2) == Z::ZERO
        }
    }

    impl Submonoid for EvenIntegers {
        type Parent = Integers;
    }

    impl Subgroup for EvenIntegers {}

    impl NormalForm<Z> for EvenIntegers {
        fn reduce(value: Z) -> Z {
            value.mod_floor(&Z::from(2))
        }
    }

    type IntegersModTwo = QuotientGroup<EvenIntegers>;

    fn modulo_two(value: impl Into<Z>) -> Quotient<Z, EvenIntegers> {
        Quotient::new(value.into())
    }

    #[test]
    fn coset_equality_is_an_equivalence_relation() {
        for a in (-3..=3).map(Z::from) {
            assert_eq!(modulo_two(a), modulo_two(a));

            for b in (-3..=3).map(Z::from) {
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
    fn coset_representatives_agree_with_the_left_coset_relation() {
        for a in (-3..=3).map(Z::from) {
            for b in (-3..=3).map(Z::from) {
                assert_eq!(
                    modulo_two(a) == modulo_two(b),
                    Modulo::<EvenIntegers>::equivalent(&Z::from(a), &Z::from(b))
                );
            }
        }

        for a in symmetries() {
            for b in symmetries() {
                assert_eq!(
                    Quotient::<Symmetry, Rotations>::new(a) == Quotient::new(b),
                    Modulo::<Rotations>::equivalent(&a, &b)
                );
            }
        }
    }

    #[test]
    fn subgroups_of_abelian_groups_are_normal() {
        fn assert_normal<N: NormalSubgroup>() {}

        assert_normal::<EvenIntegers>();
    }

    #[test]
    fn quotient_of_an_abelian_group_is_abelian() {
        fn assert_group<G: Group>() {}
        fn assert_abelian<G: AbelianGroup>() {}

        assert_group::<IntegersModTwo>();
        assert_abelian::<IntegersModTwo>();
        assert_eq!(
            IntegersModTwo::apply(modulo_two(1), modulo_two(1)),
            IntegersModTwo::identity()
        );
        assert_eq!(IntegersModTwo::inverse(modulo_two(1)), modulo_two(1));
    }

    #[test]
    fn quotient_operation_does_not_depend_on_representatives() {
        let product = IntegersModTwo::apply(modulo_two(1), modulo_two(2));
        let same_product = IntegersModTwo::apply(modulo_two(3), modulo_two(4));

        assert_eq!(product, same_product);
        assert_eq!(modulo_two(5).representative(), &Z::from(1));
        assert_eq!(modulo_two(5).into_representative(), Z::from(1));
    }

    #[test]
    fn quotient_operator_satisfies_the_group_laws() {
        for a in (-2..=2).map(Z::from) {
            let value = modulo_two(a);
            let inverse = IntegersModTwo::inverse(value.clone());

            assert_eq!(
                IntegersModTwo::apply(value.clone(), IntegersModTwo::identity()),
                value
            );
            assert_eq!(
                IntegersModTwo::apply(inverse, value.clone()),
                IntegersModTwo::identity()
            );

            for b in (-2..=2).map(Z::from) {
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

    #[derive(Clone, Copy, Debug, Eq, PartialEq, Set)]
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

    #[derive(Associative, BinaryOperator)]
    #[operator(domain = Symmetry, symbol = "*", apply = Symmetry::applied, identity = Symmetry::identity(), inverse = Symmetry::inversed, inverse_symbol = "/")]
    struct Compose;

    type D3 = (Compose,);

    struct Rotations;

    impl Subset for Rotations {
        type Superset = Symmetry;

        fn contains(value: &Symmetry) -> bool {
            !value.reflected
        }
    }

    impl Submonoid for Rotations {
        type Parent = D3;
    }

    impl Subgroup for Rotations {}
    impl NormalSubgroup for Rotations {}

    impl NormalForm<Symmetry> for Rotations {
        fn reduce(value: Symmetry) -> Symmetry {
            Symmetry::new(0, value.reflected)
        }
    }

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

    fn modulo_rotations(rotation: u8, reflected: bool) -> Quotient<Symmetry, Rotations> {
        Quotient::new(symmetry(rotation, reflected))
    }

    #[test]
    fn triangle_symmetries_satisfy_the_group_laws() {
        for a in symmetries() {
            assert_eq!(D3::apply(a, D3::identity()), a);
            assert_eq!(D3::apply(D3::identity(), a), a);
            assert_eq!(D3::apply(D3::inverse(a), a), D3::identity());
            assert_eq!(D3::apply(a, D3::inverse(a)), D3::identity());

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

        assert_eq!(product, D3ModuloRotations::identity());
        assert_eq!(product, same_product);
    }
}
