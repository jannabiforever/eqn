use std::ops::{Add, Neg};

use eqn_core::op::{Associative, BinaryOperator, Commutative, Identity, Inverse};
use eqn_core::set::Set;

#[derive(Clone, Debug, Eq, PartialEq, Set)]
struct Unit;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = i64, symbol = "+", apply = Add::add, identity = 0, inverse = Neg::neg, inverse_symbol = "-")]
struct AddSome;

fn requires<Op: Associative + Commutative>() {}
fn is_set<S: Set>() {}

#[test]
fn derives_marker_traits() {
    requires::<AddSome>();
    is_set::<Unit>();
    is_set::<i64>();
    assert_eq!(AddSome::apply(2, 3), 5);
    assert_eq!(AddSome::identity(), 0);
    assert_eq!(AddSome::inverse(4), -4);
}
