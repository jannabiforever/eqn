use std::ops::{Add, Neg};

use eqn_core::op::{Associative, BinaryOperator, Commutative, Identity, Inverse};

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = i64, symbol = "+", apply = Add::add, identity = 0, inverse = Neg::neg, inverse_symbol = "-")]
struct AddSome;

#[test]
fn a_derived_operator_applies_its_annotated_functions() {
    assert_eq!(AddSome::apply(2, 3), 5);
    assert_eq!(AddSome::identity(), 0);
    assert_eq!(AddSome::inverse(4), -4);
}
