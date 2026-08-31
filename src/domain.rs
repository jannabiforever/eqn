// ================================================================================
// Domain traits
// ================================================================================

pub trait Domain {
    // Ord gives expressions a total order for canonical (sorted) forms.
    type Element: Clone + Ord;
}

// ================================================================================
// Domains
// ================================================================================

pub struct NaturalNumber;

impl Domain for NaturalNumber {
    // TODO: use big-number like python so large numbers don't overflow
    type Element = u64;
}
