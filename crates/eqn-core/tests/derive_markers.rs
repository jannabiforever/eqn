use eqn_core::op::{AssociativeOperator, BinaryOperator, CommutativeOperator};
use eqn_core::set::Set;

struct Ints;
impl Set for Ints {
    type Element = i64;
}

#[derive(AssociativeOperator, CommutativeOperator)]
struct Add;
impl BinaryOperator for Add {
    type Domain = Ints;
    fn apply(a: i64, b: i64) -> i64 {
        a + b
    }
}

fn requires<Op: AssociativeOperator + CommutativeOperator>() {}

#[test]
fn derives_marker_traits() {
    requires::<Add>();
}
