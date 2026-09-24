use std::ops::{Add, Mul, Neg};

use eqn_core::op::{Associative, BinaryOperator, Commutative};
use eqn_core::set::{N, Q, Rational, Z};

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = N, symbol = "+", apply = Add::add, identity = N::ZERO)]
pub struct NAdd;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = N, symbol = "*", apply = Mul::mul, identity = N::from(1u8))]
pub struct NMul;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Q, symbol = "+", apply = Add::add, identity = Rational::zero(), inverse = Neg::neg, inverse_symbol = "-")]
pub struct QAdd;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Q, symbol = "*", apply = Mul::mul, identity = Rational::one(), inverse = Rational::recip, inverse_symbol = "/")]
pub struct QMul;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Z, symbol = "+", apply = Add::add, identity = Z::ZERO, inverse = Neg::neg, inverse_symbol = "-")]
pub struct ZAdd;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Z, symbol = "*", apply = Mul::mul, identity = Z::from(1))]
pub struct ZMul;

#[cfg(test)]
mod tests {
    use eqn_core::op::{Identity, Inverse};

    use super::*;

    /// `a, b, c` drawn from each domain, wide enough to leave the machine
    /// words behind.
    fn naturals() -> [N; 4] {
        [
            N::ZERO,
            N::from(1u8),
            N::from(7u8),
            N::from(2u8).pow(100) + N::from(3u8),
        ]
    }

    fn integers() -> [Z; 5] {
        [
            Z::ZERO,
            Z::from(1),
            Z::from(-7),
            Z::from(2).pow(100),
            -Z::from(3).pow(80),
        ]
    }

    fn rationals() -> [Q; 5] {
        [
            Q::zero(),
            Q::one(),
            Q::new(Z::from(-3), Z::from(4)),
            Q::new(Z::from(1), Z::from(2).pow(100)),
            Q::new(Z::from(3).pow(80), Z::from(7)),
        ]
    }

    /// Checks associativity, commutativity and the identity law of `Op` on
    /// every triple drawn from `elements`.
    fn assert_commutative_monoid_laws<Op>(elements: &[Op::Domain])
    where
        Op: BinaryOperator + Associative + Commutative + Identity,
    {
        for a in elements {
            assert_eq!(Op::apply(a.clone(), Op::identity()), *a);
            assert_eq!(Op::apply(Op::identity(), a.clone()), *a);

            for b in elements {
                assert_eq!(
                    Op::apply(a.clone(), b.clone()),
                    Op::apply(b.clone(), a.clone())
                );

                for c in elements {
                    assert_eq!(
                        Op::apply(Op::apply(a.clone(), b.clone()), c.clone()),
                        Op::apply(a.clone(), Op::apply(b.clone(), c.clone()))
                    );
                }
            }
        }
    }

    /// Checks that `inverse` undoes `Op` on both sides.
    fn assert_inverse_law<Op: Inverse>(elements: &[Op::Domain]) {
        for a in elements {
            assert_eq!(Op::apply(a.clone(), Op::inverse(a.clone())), Op::identity());
            assert_eq!(Op::apply(Op::inverse(a.clone()), a.clone()), Op::identity());
        }
    }

    #[test]
    fn natural_addition_and_multiplication_are_commutative_monoids() {
        assert_commutative_monoid_laws::<NAdd>(&naturals());
        assert_commutative_monoid_laws::<NMul>(&naturals());
    }

    #[test]
    fn integer_addition_and_multiplication_are_commutative_monoids() {
        assert_commutative_monoid_laws::<ZAdd>(&integers());
        assert_commutative_monoid_laws::<ZMul>(&integers());
    }

    #[test]
    fn rational_addition_and_multiplication_are_commutative_monoids() {
        assert_commutative_monoid_laws::<QAdd>(&rationals());
        assert_commutative_monoid_laws::<QMul>(&rationals());
    }

    #[test]
    fn negation_inverts_addition_and_reciprocal_inverts_multiplication() {
        assert_inverse_law::<ZAdd>(&integers());
        assert_inverse_law::<QAdd>(&rationals());
        assert_inverse_law::<QMul>(&rationals()[1..]);
    }

    #[test]
    fn multiplication_distributes_over_addition() {
        for a in &rationals() {
            for b in &rationals() {
                for c in &rationals() {
                    assert_eq!(
                        QMul::apply(a.clone(), QAdd::apply(b.clone(), c.clone())),
                        QAdd::apply(
                            QMul::apply(a.clone(), b.clone()),
                            QMul::apply(a.clone(), c.clone())
                        )
                    );
                }
            }
        }
    }
}
