use std::ops::{Add, Neg};

use eqn_core::op::{Associative, BinaryOperator, Commutative, Identity, Inverse};
use eqn_core::set::Set;

#[derive(Set)]
#[set(element = i64)]
struct Ints;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Ints, apply = Add::add, identity = 0, inverse = Neg::neg)]
struct AddSome;

fn requires<Op: Associative + Commutative>() {}

#[test]
fn derives_marker_traits() {
    requires::<AddSome>();
    let _: <Ints as Set>::Element = 1i64;
    assert_eq!(AddSome::apply(2, 3), 5);
    assert_eq!(AddSome::IDENTITY, 0);
    assert_eq!(AddSome::inverse(4), -4);
}
