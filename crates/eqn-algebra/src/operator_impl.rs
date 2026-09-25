use std::ops::{Add, Mul, Neg};

use eqn_core::op::{Associative, BinaryOperator, Commutative};
use eqn_core::set::{Q, Z};

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Q, symbol = "+", apply = Add::add, identity = Q::ZERO, inverse = Neg::neg, inverse_symbol = "-")]
pub struct QAdd;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Q, symbol = "*", apply = Mul::mul, identity = Q::ONE, inverse = Q::recip, inverse_symbol = "/")]
pub struct QMul;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Z, symbol = "+", apply = Add::add, identity = Z::ZERO, inverse = Neg::neg, inverse_symbol = "-")]
pub struct ZAdd;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Z, symbol = "*", apply = Mul::mul, identity = Z::ONE)]
pub struct ZMul;
