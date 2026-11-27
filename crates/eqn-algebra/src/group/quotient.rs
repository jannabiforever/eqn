use std::marker::PhantomData;

use eqn_core::op::{Associative, BinaryOperator, Commutative};
use eqn_core::quotient::{Equivalence, Quotient};

use crate::group::normal::NormalSubgroup;
use crate::group::{AbelianGroup, Group};
use crate::monoid::{Monoid, MonoidElem};

type Dom<N> = MonoidElem<<N as NormalSubgroup>::Group>;

/// The left-coset relation of a normal subgroup `N`: `a` and `b` are related
/// when `a^-1 * b` lies in `N`. The normal form of `N` must agree with it.
pub struct Modulo<N: NormalSubgroup>(PhantomData<N>);

impl<N: NormalSubgroup> Equivalence<Dom<N>> for Modulo<N> {
    fn equivalent(a: &Dom<N>, b: &Dom<N>) -> bool {
        N::contains(&N::Group::apply(N::Group::inverse(a.clone()), b.clone()))
    }
}

impl<N: NormalSubgroup> Modulo<N> {
    /// `(aN)(bN) = (ab)N`, well defined because `N` is normal.
    pub fn applied(lhs: Quotient<Dom<N>, N>, rhs: Quotient<Dom<N>, N>) -> Quotient<Dom<N>, N> {
        Quotient::new(N::Group::apply(
            lhs.into_representative(),
            rhs.into_representative(),
        ))
    }

    pub fn inversed(coset: Quotient<Dom<N>, N>) -> Quotient<Dom<N>, N> {
        Quotient::new(N::Group::inverse(coset.into_representative()))
    }

    pub fn identity() -> Quotient<Dom<N>, N> {
        Quotient::new(N::Group::identity())
    }
}

/// Multiplication of cosets of a normal subgroup.
#[derive(Associative, BinaryOperator)]
#[operator(domain = Quotient<Dom<N>, N>, symbol = <N::Group as Monoid>::SYMBOL, apply = Modulo::<N>::applied, identity = Modulo::<N>::identity(), inverse = Modulo::<N>::inversed, inverse_symbol = <N::Group as Group>::INVERSE_SYMBOL)]
pub struct QuotientOp<N: NormalSubgroup>(PhantomData<N>);

impl<N: NormalSubgroup> Commutative for QuotientOp<N> where N::Group: AbelianGroup {}

/// The quotient of a group by a normal subgroup, on the representatives `N`
/// chooses.
pub type QuotientGroup<N> = (QuotientOp<N>,);

#[cfg(test)]
mod tests {
    use eqn_core::quotient::{Congruence, NormalForm};
    use eqn_core::set::{Set, Z};
    use num_integer::Integer;

    use super::*;
    use crate::operator_impl::ZAdd;

    type Integers = (ZAdd,);

    struct EvenIntegers;

    impl NormalForm<Z> for EvenIntegers {
        fn reduce(value: Z) -> Z {
            value.mod_floor(&Z::from(2))
        }
    }

    impl Congruence<ZAdd> for EvenIntegers {}

    impl NormalSubgroup for EvenIntegers {
        type Group = Integers;
    }

    type IntegersModTwo = QuotientGroup<EvenIntegers>;

    fn modulo_two<V: Into<Z> + Clone>(value: &V) -> Quotient<Z, EvenIntegers> {
        Quotient::new(value.clone().into())
    }

    #[test]
    fn coset_equality_is_an_equivalence_relation() {
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
    fn coset_representatives_agree_with_the_left_coset_relation() {
        for a in (-3..=3).map(Z::from) {
            for b in (-3..=3).map(Z::from) {
                assert_eq!(
                    modulo_two(&a) == modulo_two(&b),
                    Modulo::<EvenIntegers>::equivalent(&Z::from(a.clone()), &Z::from(b.clone()))
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
    fn integers_modulo_two_are_their_own_inverses() {
        assert_eq!(
            IntegersModTwo::apply(modulo_two(&1), modulo_two(&1)),
            IntegersModTwo::identity()
        );
        assert_eq!(IntegersModTwo::inverse(modulo_two(&1)), modulo_two(&1));
    }

    #[test]
    fn quotient_operation_does_not_depend_on_representatives() {
        let product = IntegersModTwo::apply(modulo_two(&1), modulo_two(&2));
        let same_product = IntegersModTwo::apply(modulo_two(&3), modulo_two(&4));

        assert_eq!(product, same_product);
        assert_eq!(modulo_two(&5).representative(), &Z::from(1));
        assert_eq!(modulo_two(&5).into_representative(), Z::from(1));
    }

    #[test]
    fn reduction_mod_two_is_a_congruence_for_addition() {
        for a in (-5..=5).map(Z::from) {
            for b in (-5..=5).map(Z::from) {
                assert_eq!(
                    EvenIntegers::reduce(ZAdd::apply(a.clone(), b.clone())),
                    EvenIntegers::reduce(ZAdd::apply(
                        EvenIntegers::reduce(a.clone()),
                        EvenIntegers::reduce(b)
                    ))
                );
            }
        }
    }

    #[test]
    fn quotient_operator_satisfies_the_group_laws() {
        for a in (-2..=2).map(Z::from) {
            let value = modulo_two(&a);
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
                            IntegersModTwo::apply(modulo_two(&a), modulo_two(&b)),
                            modulo_two(&c)
                        ),
                        IntegersModTwo::apply(
                            modulo_two(&a),
                            IntegersModTwo::apply(modulo_two(&b), modulo_two(&c))
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

    impl NormalForm<Symmetry> for Rotations {
        fn reduce(value: Symmetry) -> Symmetry {
            Symmetry::new(0, value.reflected)
        }
    }

    impl Congruence<Compose> for Rotations {}

    impl NormalSubgroup for Rotations {
        type Group = D3;
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
    fn forgetting_the_rotation_is_a_congruence_for_composition() {
        for a in symmetries() {
            for b in symmetries() {
                assert_eq!(
                    Rotations::reduce(Compose::apply(a, b)),
                    Rotations::reduce(Compose::apply(Rotations::reduce(a), Rotations::reduce(b)))
                );
            }
        }
    }

    #[test]
    fn quotient_of_a_noncommutative_group_is_well_defined() {
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
