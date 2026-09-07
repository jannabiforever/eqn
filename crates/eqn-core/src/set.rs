// ================================================================================
// Domain traits
// ================================================================================

pub use eqn_macros::Set;

pub trait Set {
    // Ord gives expressions a total order for canonical (sorted) forms.
    type Element: Clone + Eq + std::fmt::Debug;
}

// ================================================================================
// Domains
// ================================================================================

pub struct NaturalNumberSet;

impl Set for NaturalNumberSet {
    // TODO: use big-number like python so large numbers don't overflow
    type Element = u64;
}
