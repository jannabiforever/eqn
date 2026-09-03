// mgca: lets `Chart` carry `[_; M::DIM]` with `DIM` an associated const.
#![feature(min_generic_const_args, macroless_generic_const_args)]
#![allow(incomplete_features)]

pub mod differential;
pub mod formatter;
pub mod group;
pub mod map;
pub mod monoid;
pub mod op;
pub mod ring;
pub mod set;
pub mod symbol;
