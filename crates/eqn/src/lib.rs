// mgca: lets `Chart` carry `[_; M::DIM]` with `DIM` an associated const.
#![feature(min_generic_const_args, macroless_generic_const_args)]
#![allow(incomplete_features)]

pub use eqn_core::{formatter, map, op, set, symbol};

pub mod differential;
pub mod group;
pub mod monoid;
pub mod ring;
