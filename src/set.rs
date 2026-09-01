// ================================================================================
// Domain traits
// ================================================================================

pub trait Set {
    // Ord gives expressions a total order for canonical (sorted) forms.
    type Element: Clone + Eq;
}

// ================================================================================
// Domains
// ================================================================================

pub struct NaturalNumberSet;

impl Set for NaturalNumberSet {
    // TODO: use big-number like python so large numbers don't overflow
    type Element = u64;
}
