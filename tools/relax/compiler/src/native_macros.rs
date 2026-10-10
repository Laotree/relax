//! Dispatch only byte-identical macro packages to the linked expansion libraries.
//! Package names alone are insufficient: workspaces can edit or replace these crates.
use crate::macro_reg::{Entry, Reg};
use relax_native_macros::Entry as Native;

static READY: std::sync::RwLock<Vec<(usize, &'static Native)>> = std::sync::RwLock::new(Vec::new());

pub fn find(entry: &Entry) -> Option<&'static Native> {
    READY.read().unwrap().iter().find(|(unit, native)| *unit == entry.unit && native.fname == entry.fname).map(|x| x.1)
}

fn matches_package(reg: &Reg, unit: usize, checked: &mut Vec<Option<bool>>) -> bool {
    if let Some(result) = checked[unit] { return result; }
    checked[unit] = Some(false); // also reject dependency cycles
    let u = &reg.units[unit];
    let Some((_, files)) = relax_native_macros::PACKAGES.iter().find(|(name, _)| *name == u.name) else { return false };
    // The wrapper's marker features have no cfg-dependent expansion code in this
    // snapshot. Implementation/helper crates have no features at all.
    let features: &[&str] = match u.name.as_str() {
        "makepad_derive_widget" => &["default", "nightly"],
        "makepad_live_id" => &["default"],
        _ => &[],
    };
    if u.edition != 2021 || !u.features.iter().all(|f| features.contains(&f.as_str())) {
        if crate::macro_reg::trace() { eprintln!("pmhost: native mismatch {} edition {} features {:?}", u.name, u.edition, u.features); }
        return false;
    }
    let Some(root) = std::path::Path::new(&u.src_path).parent().and_then(|p| p.parent()) else { return false };
    if root.join("src/lib.rs") != std::path::Path::new(&u.src_path) { return false; }
    let _why = crate::why::enabled().then(|| crate::why::enter(crate::why::Cause::new(&u.src_path, 1, "native-macro-validation", &u.name)));
    if let Some((path, _)) = files.iter().find(|(path, expected)| !crate::vfs::read(root.join(path)).map_or(false, |actual| actual == *expected)) {
        if crate::macro_reg::trace() { eprintln!("pmhost: native source mismatch {} {}", u.name, root.join(path).display()); }
        return false;
    }
    let (_, expected) = relax_native_macros::DEPENDENCIES.iter().find(|(name, _)| *name == u.name).unwrap();
    let valid = u.deps.len() == expected.len() && expected.iter().all(|name| {
        u.deps.iter().find(|(_, alias)| alias == name).map_or(false, |(dep, _)|
            reg.units[*dep].name == *name && matches_package(reg, *dep, checked))
    });
    checked[unit] = Some(valid);
    if !valid && crate::macro_reg::trace() { eprintln!("pmhost: native dependency mismatch {} {:?}", u.name, u.deps); }
    valid
}

pub fn prepare(enabled: bool) {
    let ready = if enabled {
        crate::macro_reg::REG.with(|r| {
            let r = r.borrow();
            let Some(reg) = r.as_ref() else { return Vec::new() };
            let mut checked = vec![None; reg.units.len()];
            let mut ready = Vec::new();
            for (unit, u) in reg.units.iter().enumerate().filter(|(_, u)| u.proc_macro) {
                if matches_package(reg, unit, &mut checked) {
                    ready.extend(relax_native_macros::ENTRIES.iter().filter(|n| n.krate == u.name).map(|n| (unit, n)));
                }
            }
            ready
        })
    } else { Vec::new() };
    if crate::macro_reg::trace() {
        eprintln!("pmhost: {} source-matched native entries", ready.len());
    }
    *READY.write().unwrap() = ready;
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
        assert!(matches_package(&reg, 2, &mut vec![None; 3]));
        let helper = root.join("makepad_micro_proc_macro/src/macro_lib.rs");
        let original = std::fs::read(&helper).unwrap();
        std::fs::write(&helper, b"// changed helper").unwrap();
        assert!(!matches_package(&reg, 2, &mut vec![None; 3]));
        std::fs::write(helper, original).unwrap();
        reg.units[1].deps[0].1 = "replacement".into();
        assert!(!matches_package(&reg, 2, &mut vec![None; 3]));
        reg.units[1].deps[0].1 = "makepad_micro_proc_macro".into();
        reg.units[2].features.push("different".into());
        assert!(!matches_package(&reg, 2, &mut vec![None; 3]));
    }
}
