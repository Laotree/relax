//! Token-building / parsing helpers for makepad's proc macros, over a switchable token crate:
//! `makepad_micro_proc_macro::proc_macro` is rustc's `proc_macro` normally, and a plain-data
//! `proc_macro`-compatible model with the `rapid` feature (for proc-macro libraries linked into
//! Rapid's loader). Proc-macro libraries name the token types through this re-export.

#[cfg(not(feature = "rapid"))]
pub extern crate proc_macro;

#[cfg(feature = "rapid")]
#[path = "rapid_tokens.rs"]
pub mod proc_macro;

#[allow(dead_code)]
pub mod macro_lib;
pub use macro_lib::*;
