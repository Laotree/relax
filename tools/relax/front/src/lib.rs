//! Relax's front end: parsing, the crate graph and name resolution (program), macro expansion (macros, preload,
//! derive, builtins, fmtmac, macro_reg) and immutable Rust source contexts (source_context). Builds on relax-base.
//! The layers below are re-exported, so every module of Relax is `crate::<module>` in each layer.

pub use relax_base::*;

pub mod lit;
pub mod parser;
pub mod program;
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

pub mod lang_items;
