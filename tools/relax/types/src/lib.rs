//! Relax's type layer: interned types (types), signatures and impls (tcx), type checking (typeck), layouts,
//! constant evaluation, the borrow checker, generic templates and stable type hashes. Builds on relax-front.
//! The layers below are re-exported, so every module of Relax is `crate::<module>` in each layer.

pub use relax_front::*;

pub mod types;
pub mod tcx;
pub mod type_queries;
pub mod typeck;
pub mod layout;
pub mod consteval;
pub mod borrowck;
pub mod preempt;
pub mod tytemplate;
pub mod stable;
pub mod mir;

#[cfg(test)]
mod lang_item_tests;
pub mod solve;

#[cfg(test)]
mod fnhdr_tests;

#[cfg(test)]
mod token_source_tests;
pub mod expr_use;
pub mod upvar;
pub mod region_scope;

