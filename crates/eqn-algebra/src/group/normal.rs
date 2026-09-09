use super::Subgroup;

/// A subgroup closed under conjugation by every element of its parent group.
///
/// For every `g` in the parent and `n` in the subgroup, `g * n * g^-1` must
/// belong to the subgroup.
pub trait NormalSubgroup: Subgroup {}
