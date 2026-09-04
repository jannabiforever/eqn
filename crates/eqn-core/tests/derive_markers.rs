use eqn_core::op::{Associative, BinaryOperator, Commutative};
use eqn_core::set::Set;

struct Ints;
impl Set for Ints {
    type Element = i64;
}

#[derive(Associative, Commutative)]
struct Add;
impl BinaryOperator for Add {
    type Domain = Ints;
    fn apply(a: i64, b: i64) -> i64 {
        a + b
    }
}

fn requires<Op: Associative + Commutative>() {}

#[test]
fn derives_marker_traits() {
    requires::<Add>();
}
