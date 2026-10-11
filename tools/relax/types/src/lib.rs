//! Relax's type layer: interned types (types), signatures and impls (tcx), type checking (typeck), layouts,
//! constant evaluation, the borrow checker, definition-owned body queries and stable type hashes. Builds on relax-front.
//! The layers below are re-exported, so every module of Relax is `crate::<module>` in each layer.

pub use relax_front::*;

/// memlane swap: forget the compiler generation's state held in this crate's statics;
/// called with every compiler thread quiesced, right before the old generation is destroyed.
pub fn zone_reset() {
    borrowck::lazy::zone_reset();
    tcx::resolve_bound_vars::zone_reset();
}

#[test]
fn zone_reset_fresh_process() {
    const CHILD: &str = "RELAX_ZONE_RESET_TEST_CHILD";
    if std::env::var_os(CHILD).is_some() {
        zone_reset();
        zone_reset();
        return;
    }
    // Other tests use these statics; the reset and its empty-state assertions need isolation.
    let status = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "zone_reset_fresh_process"])
        .env(CHILD, "1")
        .status().unwrap();
    assert!(status.success());
}

pub mod types;
pub mod instance;
pub mod consts;
pub mod const_eval;
pub mod tcx;
pub mod type_queries;
pub mod typeck;
pub mod layout;
pub mod const_fold;
pub mod borrowck;
pub mod stable;
pub mod mir;

#[cfg(test)]
mod lang_item_tests;
pub mod infer;

#[cfg(test)]
mod fnhdr_tests;

#[cfg(test)]
mod token_source_tests;
pub mod expr_use;
pub mod upvar;
pub mod region_scope;

pub mod next_solver;
