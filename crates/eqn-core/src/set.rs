// ================================================================================
// Domain traits
// ================================================================================

pub use eqn_macros::Set;

pub trait Set {
    // Ord gives expressions a total order for canonical (sorted) forms.
    type Element: Clone + Eq + std::fmt::Debug;
}

/// Alias for a set's element.
pub type Elem<S> = <S as Set>::Element;
