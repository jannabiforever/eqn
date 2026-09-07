use super::{CommutativeRing, RingElem};

// ================================================================================
// DifferentialRing
// ================================================================================

/// A commutative ring with a family of commuting derivations `∂_i`, indexed
/// by [`Index`](Self::Index). Each `∂_i` is additive and satisfies Leibniz,
/// `∂_i(ab) = (∂_i a) b + a (∂_i b)`, and `∂_i ∂_j = ∂_j ∂_i`.
pub trait DifferentialRing: CommutativeRing {
    /// Names a derivation.
    type Index;
    /// `∂_i a`.
    fn derive(a: RingElem<Self>, i: &Self::Index) -> RingElem<Self>;
}
