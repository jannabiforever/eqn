use crate::op::{Commutative, Inverse};
use crate::ring::{Ring, RingElem};

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
