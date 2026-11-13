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

#[cfg(test)]
mod tests {
    use super::*;
    /// A mark is visible until cleared.
    #[test]
    fn marks_are_recorded_and_cleared() {
        clear();
        assert!(marked().is_empty());
        mark("crate_a");
        mark("crate_b");
        assert_eq!(marked().iter().cloned().collect::<Vec<_>>(), vec!["crate_a", "crate_b"]);
        clear();
        assert!(marked().is_empty());
    }
}
