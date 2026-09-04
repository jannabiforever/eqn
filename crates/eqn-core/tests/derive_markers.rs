use eqn_core::op::{Associative, BinaryOperator, Commutative, Identity, Inverse};
use eqn_core::set::Set;

#[derive(Set)]
#[set(element = i64)]
struct Ints;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Ints, apply = |a, b| a + b, identity = 0, inverse = |a| -a)]
struct Add;

fn requires<Op: Associative + Commutative>() {}

#[test]
fn derives_marker_traits() {
    requires::<Add>();
    let _: <Ints as Set>::Element = 1i64;
    assert_eq!(Add::apply(2, 3), 5);
    assert_eq!(Add::IDENTITY, 0);
    assert_eq!(Add::inverse(4), -4);
}
