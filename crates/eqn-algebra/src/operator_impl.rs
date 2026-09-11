use std::ops::{Add, Mul, Neg};

use eqn_core::op::{Associative, BinaryOperator, Commutative};
use eqn_core::set::{Q, Rational, Z};

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Q, symbol = "+", apply = Add::add, identity = Rational::ZERO, inverse = Neg::neg, inverse_symbol = "-")]
pub struct QAdd;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Q, symbol = "*", apply = Mul::mul, identity = Rational::ONE, inverse = Rational::recip, inverse_symbol = "/")]
pub struct QMul;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Z, symbol = "+", apply = Add::add, identity = 0, inverse = Neg::neg, inverse_symbol = "-")]
pub struct ZAdd;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Z, symbol = "*", apply = Mul::mul, identity = 1)]
pub struct ZMul;
