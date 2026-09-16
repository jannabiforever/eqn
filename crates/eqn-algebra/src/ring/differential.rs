use super::{CommutativeRing, RingElem};

// ================================================================================
// DifferentialRing
// ================================================================================

/// A commutative ring with a family of commuting derivations `\partial_i`,
/// indexed by [`Index`](Self::Index). Each `\partial_i` is additive and
/// satisfies Leibniz, `\partial_i(ab) = (\partial_i a) b + a (\partial_i b)`,
/// and `\partial_i \partial_j = \partial_j \partial_i`.
pub trait DifferentialRing: CommutativeRing {
    /// Names a derivation.
    type Index;
    /// `\partial_i a`.
    fn derive(a: RingElem<Self>, i: &Self::Index) -> RingElem<Self>;
}
