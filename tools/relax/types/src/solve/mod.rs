//! Trait selection, inference relation, goal evaluation, and canonical interfaces.
pub mod canonical;
pub mod canonicalizer;
pub mod goal;
pub mod search_graph;
pub mod infer;
pub mod relate;
pub mod select;
pub use select::{select, evaluate, SelectionResult, Selected};
