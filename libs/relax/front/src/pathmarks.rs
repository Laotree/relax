//! Crates whose expansion produced a value that embeds a workspace absolute path
//! (`CARGO_MANIFEST_DIR`, `OUT_DIR`). The mark is a fast path for the shared-cache gate: the
//! payload scan is the truth, and the cache keeps every anchor for a marked crate until the
//! identity change lands.
use std::collections::BTreeSet;
use std::sync::{Mutex, OnceLock};

fn set() -> &'static Mutex<BTreeSet<String>> {
    static S: OnceLock<Mutex<BTreeSet<String>>> = OnceLock::new();
    S.get_or_init(|| Mutex::new(BTreeSet::new()))
}

/// Records that crate `krate` produced a workspace-path value.
pub fn mark(krate: &str) {
    set().lock().unwrap().insert(krate.to_string());
}

/// The marked crates, for the cache's identity decision.
pub fn marked() -> BTreeSet<String> {
    set().lock().unwrap().clone()
}

/// Forgets every mark (a run's reset).
pub fn clear() {
    set().lock().unwrap().clear();
}

/// A literal value that came from `env!`/`OUT_DIR` and names a workspace path. Keyed by the
/// value: a hand-written literal equal to it would also be treated as an anchored path (a rare
/// corner; the value is a path of the build itself).
fn marked_literals() -> &'static Mutex<BTreeSet<String>> {
    static L: OnceLock<Mutex<BTreeSet<String>>> = OnceLock::new();
    L.get_or_init(|| Mutex::new(BTreeSet::new()))
}

/// Records a path value produced by `env!`/`OUT_DIR` for the literal lowering.
pub fn mark_literal(v: &str) {
    marked_literals().lock().unwrap().insert(v.to_string());
}

/// Whether a literal value is such a path.
pub fn is_marked_literal(v: &str) -> bool {
    marked_literals().lock().unwrap().contains(v)
}

#[cfg(test)]
mod tests {
    use super::*;
    /// A mark is visible until cleared.
    #[test]
    fn marks_are_recorded_and_cleared() {
        clear();
        marked_literals().lock().unwrap().clear();
        assert!(marked().is_empty());
        mark("crate_a");
        mark("crate_b");
        assert_eq!(marked().iter().cloned().collect::<Vec<_>>(), vec!["crate_a", "crate_b"]);
        clear();
        marked_literals().lock().unwrap().clear();
        assert!(marked().is_empty());
    }
}
