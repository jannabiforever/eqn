// ================================================================================
// Domain traits
// ================================================================================

pub trait Domain {
    type Element: Clone + Eq + PartialEq;
}

// ================================================================================
// Domains
// ================================================================================

pub struct NaturalNumber;

impl Domain for NaturalNumber {
    // TODO: use big-number like python so large numbers don't overflow
    type Element = u64;
}
