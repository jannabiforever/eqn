use super::{AbelianGroup, Subgroup};

/// A subgroup closed under conjugation by every element of its parent group.
///
/// For every `g` in the parent and `n` in the subgroup, `g * n * g^-1` must
/// belong to the subgroup.
pub trait NormalSubgroup: Subgroup {}

/// Every subgroup of an abelian group is normal.
impl<S: Subgroup> NormalSubgroup for S where S::Parent: AbelianGroup {}
