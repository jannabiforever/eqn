use eqn_core::op::{Associative, BinaryOperator, Commutative};
use eqn_core::set::Set;

#[derive(Set)]
#[set(element = i64)]
struct Ints;

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
    let _: <Ints as Set>::Element = 1i64;
}
