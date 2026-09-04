pub use eqn_core::{map, op, rewriter, set, symbol};

pub mod group;
pub mod monoid;
pub mod ring;

/// Splices one level of nesting: items for which `split` yields `Ok(inner)`
/// are replaced by their children, the rest pass through. Allocation-free
/// (an empty `Vec` does not allocate).
pub(crate) fn flatten<T>(
    items: Vec<T>,
    split: impl Fn(T) -> Result<Vec<T>, T>,
) -> impl Iterator<Item = T> {
    items.into_iter().flat_map(move |item| {
        let (inner, leaf) = match split(item) {
            Ok(inner) => (inner, None),
            Err(leaf) => (Vec::new(), Some(leaf)),
        };
        inner.into_iter().chain(leaf)
    })
}
