//! Makepad proc macros are native-only and must match the linked package closure.
use crate::macro_reg::{Entry, Reg};
use relax_native_macros::Entry as Native;

static GRAPH: std::sync::RwLock<Option<std::sync::Arc<Reg>>> = std::sync::RwLock::new(None);

#[derive(Clone, Debug)]
pub struct Mismatch {
    package: String,
    file: String,
    reason: String,
}
impl std::fmt::Display for Mismatch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "the proc macros in this tree differ from those built into relax: rebuild relax (cargo build --release -p relax) [{}: {}: {}]", self.package, self.file, self.reason)
    }
}
impl std::error::Error for Mismatch {}

pub fn required(name: &str) -> bool {
    relax_native_macros::PACKAGES.iter().any(|(n, _)| *n == name)
}

fn matches_package(reg: &Reg, unit: usize, checked: &mut Vec<Option<bool>>) -> Result<(), Mismatch> {
    let u = &reg.units[unit];
    let error = |file: String, reason: String| Mismatch { package: u.name.clone(), file, reason };
    match checked[unit] {
        Some(true) => return Ok(()),
        Some(false) => return Err(error(u.src_path.clone(), "dependency cycle".into())),
        None => checked[unit] = Some(false),
    }
    let Some((_, files)) = relax_native_macros::PACKAGES.iter().find(|(name, _)| *name == u.name) else {
        return Err(error(u.src_path.clone(), "dependency is not built into relax".into()));
    };
    if u.proc_macro != relax_native_macros::ENTRIES.iter().any(|n| n.krate == u.name) {
        return Err(error(u.src_path.clone(), "proc-macro crate kind differs".into()));
    }
    let features: &[&str] = match u.name.as_str() {
        "makepad_derive_widget" => &["default", "nightly"],
        "makepad_live_id" => &["default"],
        _ => &[],
    };
    if u.edition != 2021 || !u.features.iter().all(|f| features.contains(&f.as_str())) {
        return Err(error(u.src_path.clone(), format!("edition {} or features {:?} differ", u.edition, u.features)));
    }
    let root = std::path::Path::new(&u.src_path).parent().and_then(|p| p.parent())
        .ok_or_else(|| error(u.src_path.clone(), "invalid package root".into()))?;
    if root.join("src/lib.rs") != std::path::Path::new(&u.src_path) {
        return Err(error(u.src_path.clone(), "crate root is not src/lib.rs".into()));
    }
    let _why = crate::why::enabled().then(|| crate::why::enter(crate::why::Cause::new(&u.src_path, 1, "native-macro-validation", &u.name)));
    for (path, expected) in *files {
        let path = root.join(path);
        let actual = crate::vfs::read_shared(&path).map_err(|e| error(path.display().to_string(), e.to_string()))?;
        if actual.as_ref() != *expected {
            return Err(error(path.display().to_string(), "source bytes differ".into()));
        }
    }
    // Additions matter as well as modified/deleted embedded inputs.
    let mut dirs = vec![root.join("src")];
    while let Some(dir) = dirs.pop() {
        for (path, is_dir) in crate::vfs::read_dir(&dir).map_err(|e| error(dir.display().to_string(), e.to_string()))? {
            let path = dir.join(path);
            if is_dir { dirs.push(path); }
            else if !files.iter().any(|(relative, _)| root.join(relative) == path) {
                return Err(error(path.display().to_string(), "source file was added".into()));
            }
        }
    }
    if crate::vfs::exists(root.join("build.rs")) && !files.iter().any(|(p, _)| *p == "build.rs") {
        return Err(error(root.join("build.rs").display().to_string(), "build script was added".into()));
    }
    let (_, expected) = relax_native_macros::DEPENDENCIES.iter().find(|(name, _)| *name == u.name).unwrap();
    if u.deps.len() != expected.len() {
        return Err(error(root.join("Cargo.toml").display().to_string(), "dependency count differs".into()));
    }
    for name in *expected {
        let (dep, _) = u.deps.iter().find(|(_, alias)| alias == name)
            .ok_or_else(|| error(root.join("Cargo.toml").display().to_string(), format!("missing dependency alias {name}")))?;
        if reg.units[*dep].name != *name {
            return Err(error(root.join("Cargo.toml").display().to_string(), format!("dependency {name} resolves to {}", reg.units[*dep].name)));
        }
        matches_package(reg, *dep, checked)?;
    }
    checked[unit] = Some(true);
    Ok(())
}

/// Revalidate at use, including after boot's native table would have become stale.
/// Errors are never interpreted as permission to enter the JIT macro world.
pub fn find(entry: &Entry) -> Result<Option<&'static Native>, String> {
    let reads = crate::vfs::ReadSnapshot::new(false);
    let _reads = reads.bind();
    let reg = GRAPH.read().unwrap().clone().ok_or("proc macro graph is not registered")?;
    find_in(&reg, entry)
}

fn find_in(reg: &Reg, entry: &Entry) -> Result<Option<&'static Native>, String> {
    let u = &reg.units[entry.unit];
    if !required(&u.name) { return Ok(None); }
    matches_package(reg, entry.unit, &mut vec![None; reg.units.len()]).map_err(|e| e.to_string())?;
    relax_native_macros::ENTRIES.iter().find(|n| n.krate == u.name && n.fname == entry.fname)
        .map(Some).ok_or_else(|| Mismatch { package: u.name.clone(), file: u.src_path.clone(), reason: format!("entry {} is not built into relax", entry.fname) }.to_string())
}

pub fn prepare() -> Result<(), String> {
    let reads = crate::vfs::ReadSnapshot::new(false);
    let _reads = reads.bind();
    *GRAPH.write().unwrap() = None;
    let reg = crate::macro_reg::REG.with(|r| r.borrow().clone());
    let Some(reg) = reg else { return Ok(()) };
    let mut checked = vec![None; reg.units.len()];
    let mut count = 0;
    for (unit, u) in reg.units.iter().enumerate().filter(|(_, u)| required(&u.name)) {
        matches_package(&reg, unit, &mut checked).map_err(|e| e.to_string())?;
        count += relax_native_macros::ENTRIES.iter().filter(|n| n.krate == u.name).count();
        for (_, entry) in reg.derives.iter().chain(&reg.macros).filter(|(_, e)| e.unit == unit) {
            if !relax_native_macros::ENTRIES.iter().any(|n| n.krate == u.name && n.fname == entry.fname) {
                return Err(Mismatch { package: u.name.clone(), file: u.src_path.clone(), reason: format!("entry {} is not built into relax", entry.fname) }.to_string());
            }
        }
    }
    if crate::macro_reg::trace() { eprintln!("pmhost: {count} source-matched native entries"); }
    *GRAPH.write().unwrap() = Some(std::sync::Arc::new(reg));
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn native_requires_the_complete_source_and_dependency_identity() {
        use crate::macro_reg::UnitInfo;
        let root = std::env::temp_dir().join(format!("relax-native-{}-{}", std::process::id(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        struct Cleanup(std::path::PathBuf);
        impl Drop for Cleanup { fn drop(&mut self) { let _ = std::fs::remove_dir_all(&self.0); } }
        let _cleanup = Cleanup(root.clone());
        let mut reg = Reg::default();
        for name in ["makepad_micro_proc_macro", "makepad_micro_serde_derive_impl", "makepad_micro_serde_derive"] {
            let (_, files) = relax_native_macros::PACKAGES.iter().find(|(n, _)| *n == name).unwrap();
            for (path, bytes) in *files {
                let path = root.join(name).join(path);
                std::fs::create_dir_all(path.parent().unwrap()).unwrap();
                std::fs::write(path, bytes).unwrap();
            }
            let unit = reg.units.len();
            reg.units.push(UnitInfo { name: name.into(), src_path: root.join(name).join("src/lib.rs").to_string_lossy().into_owned(), edition: 2021,
                features: Vec::new(), deps: if unit == 0 { Vec::new() } else { vec![(unit - 1, reg.units[unit - 1].name.clone())] }, proc_macro: unit == 2 });
        }
        reg.units[2].deps.push((0, "makepad_micro_proc_macro".into()));
        assert!(matches_package(&reg, 2, &mut vec![None; 3]).is_ok());
        let native = relax_native_macros::ENTRIES.iter().find(|n| n.krate == reg.units[2].name).unwrap();
        let entry = Entry { unit: 2, fname: native.fname.into(), kind: crate::macro_reg::Kind::Derive };
        assert!(find_in(&reg, &entry).unwrap().is_some());
        let missing = Entry { fname: "missing_native_entry".into(), ..entry.clone() };
        assert!(find_in(&reg, &missing).err().unwrap().contains("entry missing_native_entry is not built into relax"));
        let helper = root.join("makepad_micro_proc_macro/src/macro_lib.rs");
        let original = std::fs::read(&helper).unwrap();
        std::fs::write(&helper, b"// changed helper").unwrap();
        let mismatch = matches_package(&reg, 2, &mut vec![None; 3]).unwrap_err();
        assert_eq!(mismatch.package, "makepad_micro_proc_macro");
        assert_eq!(mismatch.file, helper.to_string_lossy());
        assert_eq!(mismatch.reason, "source bytes differ");
        // A previously certified entry must fail on late/reload expansion too.
        assert!(find_in(&reg, &entry).err().unwrap().contains("source bytes differ"));
        assert!(mismatch.to_string().contains("the proc macros in this tree differ from those built into relax: rebuild relax (cargo build --release -p relax)"));
        std::fs::write(helper, original).unwrap();
        reg.units[1].deps[0].1 = "replacement".into();
        assert!(matches_package(&reg, 2, &mut vec![None; 3]).unwrap_err().reason.contains("dependency alias"));
        reg.units[1].deps[0].1 = "makepad_micro_proc_macro".into();
        reg.units[2].features.push("different".into());
        assert!(matches_package(&reg, 2, &mut vec![None; 3]).unwrap_err().reason.contains("features"));
        reg.units[2].features.clear();
        reg.units[2].edition = 2018;
        assert!(matches_package(&reg, 2, &mut vec![None; 3]).unwrap_err().reason.contains("edition"));
        reg.units[2].edition = 2021;
        let added = root.join("makepad_micro_proc_macro/src/added.rs");
        std::fs::write(&added, b"// newly added input").unwrap();
        assert_eq!(matches_package(&reg, 2, &mut vec![None; 3]).unwrap_err().reason, "source file was added");
        std::fs::remove_file(&added).unwrap();
        assert!(matches_package(&reg, 2, &mut vec![None; 3]).is_ok());
    }
}
