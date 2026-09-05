// ================================================================================
// Domain traits
// ================================================================================

pub use eqn_macros::Set;

pub trait Set {
    // Ord gives expressions a total order for canonical (sorted) forms.
    type Element: Clone + Eq + std::fmt::Debug;
}
