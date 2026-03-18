// If anyone is iterating over a hash type, we want them to explicitly
// disable the warning to track possible sources of non-determinism.
#![warn(clippy::iter_over_hash_type)]
// Warn about dangerous unchecked integer conversions.
#![warn(clippy::cast_possible_truncation)]
#![warn(clippy::cast_possible_wrap)]

extern crate self as biodivine_algo_smt_inference;

pub mod bn_inference;
pub mod deprecated;
pub mod smt_solver;
