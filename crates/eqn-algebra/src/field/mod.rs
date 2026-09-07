use crate::op::{Commutative, Inverse};
use crate::ring::{Ring, RingElem, Subring};

// ================================================================================
// Field
// ================================================================================

/// A field: a commutative ring whose multiplication has inverses for every
/// element except `ZERO`. `invert(ZERO)` is a contract violation, not an
/// error; the operator's `Inverse` impl is only consulted for non-zero input.
pub trait Field: Ring<Multiplication: Commutative + Inverse> {
    fn invert(a: RingElem<Self>) -> RingElem<Self> {
        <Self::Multiplication as Inverse>::inverse(a)
    }
}

/// Any ring whose multiplication is commutative and invertible is a field
/// for free.
impl<R> Field for R
where
    R: Ring,
    R::Multiplication: Commutative + Inverse,
{
}

/// A subring of a field that is closed under inversion of nonzero elements.
pub trait Subfield: Subring<Parent: Field> {}

#[cfg(test)]
mod tests {
    use eqn_core::set::{Q, Rational};

    use super::*;
    use crate::operator_impl::{QAdd, QMul};
    use crate::ring::SubSemiRing;

    type Rationals = (Q, QAdd, QMul);

    struct AllRationals;

    impl SubSemiRing for AllRationals {
        type Parent = Rationals;

        fn contains(_: &RingElem<Self::Parent>) -> bool {
            true
        }
    }

    impl Subring for AllRationals {}
    impl Subfield for AllRationals {}

    #[test]
    fn rationals_form_a_subfield() {
        fn assert_subfield<S: Subfield>() {}

        assert_subfield::<AllRationals>();
        for value in [Rational::from(-3), Rational::from(1), Rational::from(4)] {
            assert!(AllRationals::contains(&Rationals::invert(value)));
        }
    }
}
