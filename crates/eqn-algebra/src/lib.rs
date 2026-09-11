// mgca: `FiniteExtension<M>` hold `M::DIM` coordinates.
#![feature(min_generic_const_args, macroless_generic_const_args)]
#![allow(incomplete_features)]

pub use eqn_core::{map, op, rewriter, set, symbol};

pub mod algebra;
pub mod field;
pub mod group;
pub mod module;
pub mod monoid;
pub mod operator_impl;
pub mod ring;

/// Splices one level of nesting: items for which `split` yields `Ok(inner)`
/// are replaced by their children, the rest pass through. Allocation-free
/// (an empty `Vec` does not allocate).
pub(crate) trait Flatten<T> {
    fn flatten(self, split: impl Fn(T) -> Result<Vec<T>, T>) -> impl Iterator<Item = T>;
}

impl<T> Flatten<T> for Vec<T> {
    fn flatten(self, split: impl Fn(T) -> Result<Vec<T>, T>) -> impl Iterator<Item = T> {
        self.into_iter().flat_map(move |item| {
            let (inner, leaf) = match split(item) {
                Ok(inner) => (inner, None),
                Err(leaf) => (Vec::new(), Some(leaf)),
            };
            inner.into_iter().chain(leaf)
        })
    }
}
