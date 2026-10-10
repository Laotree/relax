//! Source identity of a provided crate (provided.rs): a hash of the crate's package and every
//! library dependency it reaches (proc macros included, build scripts not), each package by its
//! enabled features and either its name@version (a registry or git package: immutable) or the
//! content of its directory (a path package: every file, nested packages, `target` and hidden
//! entries left out). The loader's build.rs computes it from `cargo metadata` of its own build
//! (that is what rustc compiled into the binary); `relax run` computes it from the program's
//! unit graph. A provided crate binds only when both agree: a dev edit, another checkout or a
//! patched dependency makes Relax compile the crate from source instead.
//! Shared with the bootloader's build.rs through #[path]: std only.

/// One package of the graph: `deps` index the same slice.
pub struct SrcPkg {
    pub name: String,
    pub version: String,
    pub dir: String,
    pub features: Vec<String>,
    pub deps: Vec<usize>,
    /// a proc-macro package: it and what it reaches run at expansion time (host side)
    pub proc_macro: bool,
}

/// Features that select the shim file only (`host-shims`): the loader's build enables them,
/// a program never does, and they change no code a program calls.
const IGNORED_FEATURES: &[&str] = &["host-shims"];

struct H(u64);

impl H {
    fn bytes(&mut self, b: &[u8]) {
        let mut h = self.0 ^ (b.len() as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
        let mut chunks = b.chunks_exact(8);
        for c in &mut chunks {
            let w = u64::from_le_bytes([c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7]]);
            h = (h ^ w).wrapping_mul(0xff51_afd7_ed55_8ccd);
            h ^= h >> 32;
        }
        for &x in chunks.remainder() {
            h = (h ^ x as u64).wrapping_mul(0x0100_0000_01b3);
        }
        self.0 = (h ^ (h >> 29)).wrapping_mul(0xc4ce_b9fe_1a85_ec53);
    }
}

fn immutable(dir: &str) -> bool {
    dir.contains("/.cargo/registry/") || dir.contains("/.cargo/git/")
}

/// The files of the package at `dir` that its identity reads (relative name, path).
pub fn files(dir: &std::path::Path, rel: &str, out: &mut Vec<(String, std::path::PathBuf)>) {
    let Ok(rd) = crate::vfs::read_dir(dir) else { return };
    for (name, is_dir) in rd {
        if name.starts_with('.') {
            continue;
        }
        let p = dir.join(&name);
        let r = if rel.is_empty() { name.clone() } else { format!("{}/{}", rel, name) };
        if is_dir {
            if name == "target" || crate::vfs::is_file(p.join("Cargo.toml")) {
                continue;
            }
            files(&p, &r, out);
        } else if crate::vfs::is_file(&p) {
            out.push((r, p));
        }
    }
}

/// A package's own identity (without its dependencies). Host-side packages (a proc macro and
/// what it reaches) count without their features: cargo resolves those apart from the target
/// side (resolver 2), which `cargo metadata` does not show, and their source decides the
/// expansion.
pub fn pkg_hash(p: &SrcPkg, host: bool) -> u64 {
    let mut h = H(0x5eed);
    h.bytes(p.name.replace('-', "_").as_bytes());
    let mut feats: Vec<&str> = p.features.iter().map(|f| f.as_str()).filter(|f| !host && !IGNORED_FEATURES.contains(f)).collect();
    feats.sort_unstable();
    feats.dedup();
    for f in feats {
        h.bytes(f.as_bytes());
    }
    if immutable(&p.dir) {
        h.bytes(p.version.as_bytes());
        return h.0;
    }
    let mut fs = Vec::new();
    files(std::path::Path::new(&p.dir), "", &mut fs);
    fs.sort();
    for (rel, path) in fs {
        h.bytes(rel.as_bytes());
        h.bytes(&crate::vfs::read(&path).unwrap_or_default());
    }
    h.0
}

/// The identity of package `root` with everything it reaches. `name` per package is what is
/// compared, so the two sides may list packages in any order.
pub fn closure_hash(pkgs: &[SrcPkg], root: usize) -> u64 {
    let mut seen = vec![[false; 2]; pkgs.len()];
    let mut stack = vec![(root, false)];
    let mut parts: Vec<(String, u64)> = Vec::new();
    while let Some((i, host)) = stack.pop() {
        if i >= pkgs.len() {
            continue;
        }
        let host = host || pkgs[i].proc_macro;
        if std::mem::replace(&mut seen[i][host as usize], true) {
            continue;
        }
        parts.push((format!("{}{}@{}", if host { "host:" } else { "" }, pkgs[i].name.replace('-', "_"), pkgs[i].version), pkg_hash(&pkgs[i], host)));
        stack.extend(pkgs[i].deps.iter().map(|d| (*d, host)));
    }
    parts.sort();
    parts.dedup();
    if std::env::var_os("RELAX_SRC_TRACE").is_some() {
        for (n, x) in &parts {
            eprintln!("srchash {} {} {:016x}", pkgs[root].name, n, x);
        }
    }
    let mut h = H(0x9d0);
    for (n, x) in parts {
        h.bytes(n.as_bytes());
        h.bytes(&x.to_le_bytes());
    }
    h.0
}
