//! Inputs whose identity cannot be replaced by a live body transaction. Snapshot before
//! loading, so a checkout during load/parse is still observed when the watcher starts.
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

pub(super) type Stamp = Option<(std::time::SystemTime, u64)>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Kind {
    Source(String),
    Provided,
    Build,
    Manifest,
    Std,
}

#[derive(Default)]
pub struct Inputs {
    pub(super) paths: BTreeMap<String, (Stamp, Kind)>,
}

impl Inputs {
    fn insert(&mut self, path: &Path, kind: Kind) {
        let path = path.to_string_lossy().into_owned();
        let stamp = super::stamp(&path);
        self.paths.insert(path, (stamp, kind));
    }

    pub fn collect(graph: &crate::unitgraph::Graph, std_dir: &str, workspace: &str) -> Self {
        let mut inputs = Self::default();
        let mut dirs = BTreeSet::new();
        for (dir, name, _) in &graph.pkg {
            if dir.is_empty() || dir.contains("/.cargo/registry/") || dir.contains("/.cargo/git/") || !dirs.insert(dir) { continue; }
            let provided = crate::provided::registered(name);
            let mut files = Vec::new();
            crate::srchash::files(Path::new(dir), "", &mut files);
            for (rel, path) in files {
                let kind = if matches!(rel.as_str(), "Cargo.toml" | "Cargo.lock") {
                    Kind::Manifest
                } else if provided {
                    Kind::Provided
                } else if path.extension().is_some_and(|x| x == "rs") {
                    Kind::Source(dir.clone())
                } else { continue };
                inputs.insert(&path, kind);
            }
            // Include an absent lockfile too: creating it changes the resolved graph.
            inputs.insert(&Path::new(dir).join("Cargo.lock"), Kind::Manifest);
        }
        for script in &graph.build_scripts {
            inputs.insert(Path::new(&script.src_path), Kind::Build);
        }
        for name in ["Cargo.toml", "Cargo.lock"] {
            inputs.insert(&Path::new(workspace).join(name), Kind::Manifest);
        }
        let mut files = Vec::new();
        crate::srchash::files(Path::new(std_dir), "", &mut files);
        for (_, path) in files { inputs.insert(&path, Kind::Std); }
        inputs
    }

    pub(super) fn restart_reason<'a>(&self, paths: impl Iterator<Item = &'a str>) -> Option<&'static str> {
        let mut packages = BTreeSet::new();
        let mut reason = None;
        for path in paths {
            match self.paths.get(path).map(|x| &x.1) {
                Some(Kind::Provided) => return Some("the Splash VM or other provided sources changed: rebuild relax"),
                Some(Kind::Std) => reason = Some("Relax's std changed"),
                Some(Kind::Manifest) => { if reason.is_none() { reason = Some("the Cargo graph changed"); } }
                Some(Kind::Build) => { if reason.is_none() { reason = Some("a build script changed"); } }
                Some(Kind::Source(package)) => { packages.insert(package); }
                None => {}
            }
        }
        // A transaction spanning package ownership boundaries can be a partial checkout.
        // There is no atomic filesystem snapshot tying those packages to the loaded graph.
        // Keep running the old program; this is a reload policy, not a capacity limit.
        reason.or_else(|| (packages.len() > 1).then_some("sources in multiple packages changed (e.g. a git checkout)"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn package_boundary_and_non_patchable_inputs() {
        let mut inputs = Inputs::default();
        inputs.insert(Path::new("app/a.rs"), Kind::Source("app".into()));
        inputs.insert(Path::new("app/b.rs"), Kind::Source("app".into()));
        inputs.insert(Path::new("dep/c.rs"), Kind::Source("dep".into()));
        assert_eq!(inputs.restart_reason(["app/a.rs", "app/b.rs"].into_iter()), None);
        assert!(inputs.restart_reason(["app/a.rs", "dep/c.rs"].into_iter()).is_some());
        for kind in [Kind::Provided, Kind::Build, Kind::Manifest, Kind::Std] {
            inputs.insert(Path::new("changed"), kind);
            assert!(inputs.restart_reason(["changed"].into_iter()).is_some());
        }
    }
}
