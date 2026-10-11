//! Relax's front end: parsing, the crate graph and name resolution (program), macro expansion (macros, preload,
//! derive, builtins, fmtmac, macro_reg) and immutable Rust source contexts (source_context). Builds on relax-base.
//! The layers below are re-exported, so every module of Relax is `crate::<module>` in each layer.

pub use relax_base::*;

/// memlane swap: forget the compiler generation's state held in this crate's statics;
/// called with every compiler thread quiesced, right before the old generation is destroyed.
pub fn zone_reset() {
    program::zone_reset();
    builtins::zone_reset();
    macro_reg::zone_reset();
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

pub mod lit;
pub mod parser;
pub mod program;
pub mod def_collector;
pub mod assoc;
pub mod macros;
pub mod preload;
pub mod crate_image;
pub mod collected;
pub mod builtins;
pub mod crates;
pub mod unitgraph;
pub mod macro_reg;
pub mod census;
pub mod surface;
pub mod bitflags_native;
pub mod source_context;
pub mod rs_index;
pub mod rs_outline;

pub mod parse_work;
pub mod load_profile;
pub mod exec_profile;

pub mod diagnostics;
pub mod source;
pub mod origin_table;

pub mod lang_items;
pub mod target_features;
