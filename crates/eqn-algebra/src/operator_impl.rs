use eqn_core::op::{Associative, BinaryOperator, Commutative};
use eqn_core::set::{Q, Rational, Z};

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Q, apply = |a, b| a + b, identity = Rational::ZERO, inverse = std::ops::Neg::neg)]
pub struct QAdd;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Q, apply = |a, b| a * b, identity = Rational::ONE, inverse = Rational::recip)]
pub struct QMul;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Z, apply = |a, b| a + b, identity = 0, inverse = |a| -a)]
pub struct ZAdd;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Z, apply = |a, b| a * b, identity = 1)]
pub struct ZMul;
