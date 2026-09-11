use std::ops::{Add, Mul, Neg};

use eqn_core::set::{Q, Rational, Z};

use crate::op::{Associative, BinaryOperator, Commutative};

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Q, apply = Add::add, identity = Rational::ZERO, inverse = Neg::neg)]
pub struct QAdd;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Q, apply = Mul::mul, identity = Rational::ONE, inverse = Rational::recip)]
pub struct QMul;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Z, apply = Add::add, identity = 0, inverse = Neg::neg)]
pub struct ZAdd;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Z, apply = Mul::mul, identity = 1)]
pub struct ZMul;
