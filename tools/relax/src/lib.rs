//! The loader (the `relax` binary is `main()` of this library; the Android host library, tools/relax/android_host,
//! is the same loader as a shared object): Relax (relax; makepad's proc macros JIT-compiled by its host, macros.rs
//! sets the lexer's `script_mod!` extension) and the provided crates. Same commands and flags as `relax` (`run <package> [cargo flags]
//! [-- args]` in a workspace), plus `run <git url>[#ref] [--mount <dir>=<git url>[#ref]]...
//! [--cached] <package> ...` and `fetch <spec>` (generic git fetching, fetch.rs). Which
//! repositories to run is always given on the command line; the makepad entry scripts name the
//! runner's (tools/relax/entry/).

// macros.rs names Relax's lexer by this path
mod lexer {
    pub use relax_compiler::lexer::*;
}
mod cef;
pub mod fetch;
mod hal_host;
mod help;
mod macros;
mod remote;

/// What this loader was built from (build.rs; the linked compiler's own stamp is
/// relax_compiler::PROVENANCE).
const PROVENANCE: &str = env!("RELAX_PROVENANCE");

/// The loader binary. Usually this process's executable; but an app the runner starts runs
/// from its own macOS bundle (`<runner data>/bundles/<app>.app/Contents/MacOS/<Name>`, a hard
/// link to the loader, or a copy when it is on another volume) so the Dock shows the app's name
/// and icon. Then RELAX_LOADER, inherited from the runner, names the loader itself: it is kept
/// when it is the same file (same inode) or the same bytes, and everything the loader finds next
/// to itself (the Builder's folder, the runner's checkout and std) is found next to that one.
pub(crate) fn loader_exe() -> Option<std::path::PathBuf> {
    static EXE: std::sync::OnceLock<Option<std::path::PathBuf>> = std::sync::OnceLock::new();
    EXE.get_or_init(|| {
        let exe = plain(std::env::current_exe().and_then(|e| e.canonicalize()).ok()?);
        if let Some(named) = std::env::var_os("RELAX_LOADER").map(std::path::PathBuf::from) {
            if let Ok(named) = named.canonicalize().map(plain) {
                if named != exe && same_binary(&named, &exe) {
                    return Some(named);
                }
            }
        }
        Some(exe)
    })
    .clone()
}

/// Windows: canonicalize answers a verbatim path (`\\?\C:\...`), in which `/` is no separator, so
/// everything joined to it later (`tools/relax/compiler/std`, `/core/lib.rs`) would not
/// open; a plain drive path is the same file (as the dunce crate does). Elsewhere unchanged.
fn plain(p: std::path::PathBuf) -> std::path::PathBuf {
    #[cfg(windows)]
    {
        let s = p.to_string_lossy();
        if let Some(rest) = s.strip_prefix(r"\\?\") {
            let b = rest.as_bytes();
            if b.len() >= 3 && b[0].is_ascii_alphabetic() && b[1] == b':' && b[2] == b'\\' {
                return std::path::PathBuf::from(rest.to_string());
            }
        }
    }
    p
}

fn same_binary(a: &std::path::Path, b: &std::path::Path) -> bool {
    let (Ok(ma), Ok(mb)) = (std::fs::metadata(a), std::fs::metadata(b)) else { return false };
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        if ma.dev() == mb.dev() && ma.ino() == mb.ino() {
            return true;
        }
    }
    ma.len() == mb.len() && matches!((std::fs::read(a), std::fs::read(b)), (Ok(x), Ok(y)) if x == y)
}

/// The loader's command line: `std::env::args` of this process.
pub fn main() {
    run(relax_compiler::os::proc::args_bytes())
}

/// What the loader sets up before it runs a package, for an embedder whose process is not the
/// loader's executable (the Android host library in an Activity's process): `exe` is Relax's own
/// executable, which build scripts and `RELAX_LOADER` programs run as.
pub fn init_embedded(exe: &std::path::Path) {
    relax_compiler::unitgraph::set_self_exe(exe.to_path_buf());
    // the program's argv[0] / current_exe: the embedder has no command line of its own
    {
        use std::os::unix::ffi::OsStrExt;
        relax_compiler::os::proc::set_args(vec![exe.as_os_str().as_bytes().to_vec()]);
    }
    std::env::set_var("RELAX_LOADER", exe);
    std::env::set_var("MAKEPAD_LOADER_STATE", fetch::home().join("relax_cache"));
    macros::register();
}

/// The loader's command line as an embedder gives it. A host library loaded into another process
/// (the Android APK's executable dlopens it for build scripts) has no process arguments of its
/// own; this names them for everything that reads them (relax_compiler::os::proc::args_bytes).
pub fn run_with_args(args: Vec<Vec<u8>>) {
    relax_compiler::os::proc::set_args(args.clone());
    run(args)
}

fn run(raw_args: Vec<Vec<u8>>) {
    // CEF started this loader as a subprocess of the program it runs (cef.rs)
    if let Some(code) = cef::subprocess() {
        std::process::exit(code);
    }
    // the boot thread compiles: its allocations go to the compiler arena (JIT calls switch back)
    let _phase = relax_compiler::zone_alloc::compiler();
    relax_compiler::clock::mark_process_start();
    // a build script's RUSTC (Relax itself) asked for its version
    if relax_compiler::relax_as_rustc() {
        return;
    }
    // a child started in a virtual folder of a git repository run gets the mount table
    if let Err(e) = relax_compiler::vfs::mount_from_env() {
        eprintln!("relax: RELAX_VFS: {e}");
        std::process::exit(2);
    }
    let mut raw_args = raw_args;
    if take_privileged(&mut raw_args) {
        PRIVILEGED.store(true, std::sync::atomic::Ordering::Relaxed);
        relax_compiler::os::proc::set_args(raw_args.clone());
    }
    let args: Vec<String> = raw_args.iter().map(|a| String::from_utf8_lossy(a).into_owned()).collect();
    if args.get(1).map(String::as_str) == Some("--version") {
        println!("makepad {} (compiler: {})", PROVENANCE, relax_compiler::PROVENANCE);
        return;
    }
    // every program this loader runs (and every program those start) finds it here: a program
    // runs under the loader when its own executable is this file (std::env::current_exe), and
    // starts other apps with `$RELAX_LOADER run ...` (std process.rs: a spawn of the loader
    // with `run` arguments is a launch, never a re-run of the program)
    if let Some(e) = loader_exe() {
        std::env::set_var("RELAX_LOADER", e);
    }
    // one folder for everything Relax and the runner keep: $RELAX_HOME/relax_cache (the entry
    // scripts set RELAX_HOME to the launcher's folder); the runner's Builder library keeps its
    // records there too (MAKEPAD_LOADER_STATE)
    std::env::set_var("MAKEPAD_LOADER_STATE", fetch::home().join("relax_cache"));
    macros::register();
    match args.get(1).map(String::as_str) {
        None => {
            help::print_main(help::Stream::Err);
            std::process::exit(2);
        }
        Some("-h") | Some("--help") => {
            help::print_main(help::Stream::Out);
            std::process::exit(0);
        }
        Some("help") => std::process::exit(help::help(&args[2..])),
        // `inspect <pid|app|all|list> <command>`: ask a running app (no compiler started here)
        Some("inspect") => std::process::exit(relax_compiler::inspect::client::main(&args[2..])),
        // the remote hub: `hub [--listen <addr>]`, `remote-relay [--dial ..]`, `remote add|pair|list`
        Some("hub") => std::process::exit(remote::hub(&args[2..])),
        Some("remote-relay") => std::process::exit(remote::relay(&args[2..])),
        Some("remote") => std::process::exit(remote::remote(&args[2..])),
        // `pack-src [--target <triple>] <out.store> <package>...`: the source archive `run --src` runs from
        Some("pack-src") => match relax_compiler::packsrc::parse_args(&args[2..]).and_then(relax_compiler::packsrc::run) {
            Ok(()) => std::process::exit(0),
            Err(e) => {
                eprintln!("relax: pack-src: {e}");
                std::process::exit(1);
            }
        },
        // `run --src <store>[@<offset>+<len>] <package> ...`: from a packed source archive, no checkout
        Some("run") if args[2..].iter().any(|a| a == "--src") => std::process::exit(run_src(&args[2..])),
        // `run <git url>[#ref] [--mount <dir>=<git url>[#ref]]... [--cached] <package> ...`
        Some("run") => match fetch::split_args(&args[2..]) {
            None => {}
            Some(Err(e)) => {
                eprintln!("relax: {e}");
                std::process::exit(2);
            }
            Some(Ok((opts, spec, cached, rest))) => std::process::exit(run_spec(opts, &spec, cached, rest)),
        },
        // `fetch <git url>[#ref] [--mount ..]`: the snapshot's folder on stdout
        Some("fetch") => match fetch::split_args(&args[2..]) {
            Some(Ok((_, spec, _, rest))) if rest.is_empty() => match fetch::fetch(&fetch::home(), &spec) {
                Ok(snap) => {
                    for (dir, store, commit) in &snap.parts {
                        println!("{}\t{}\t{}", if dir.is_empty() { "." } else { dir }, store.display(), relax_compiler::gitstore::hex(commit));
                    }
                    std::process::exit(0)
                }
                Err(e) => {
                    eprintln!("relax: {e}");
                    std::process::exit(1)
                }
            },
            Some(Err(e)) => {
                eprintln!("relax: {e}");
                std::process::exit(2);
            }
            _ => {
                eprintln!("relax: usage: fetch <git url>[#ref] [--mount <dir>=<git url>[#ref]]...");
                std::process::exit(2);
            }
        },
        Some(w) if !w.starts_with('-') && !help::COMMANDS.contains(&w) => std::process::exit(help::unknown(w)),
        _ => {}
    }
    // `run <package>` in a checkout: the package's run-env first (it decides what is provided)
    if args.get(1).map(String::as_str) == Some("run") {
        if let (Some(pkg), Ok(cwd)) = (run_package(&args[2..]), std::env::current_dir()) {
            apply_run_env(&cwd.display().to_string(), &pkg);
        }
    }
    provided();
    let sess = relax_compiler::session_from_env(&args);
    relax_compiler::cli_main(&sess);
}

/// `relax run --privileged ..`: the booted app is granted the HAL's domain control (hal_host.rs).
/// The host's own flag: taken out of the command line here, before anything else reads it.
static PRIVILEGED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Removes `--privileged` from among the options of a `run` (before its package); whether it was there.
fn take_privileged(raw: &mut Vec<Vec<u8>>) -> bool {
    if raw.get(1).map(Vec::as_slice) != Some(b"run".as_slice()) {
        return false;
    }
    let mut i = 2;
    while i < raw.len() {
        match raw[i].as_slice() {
            b"--privileged" => {
                raw.remove(i);
                return true;
            }
            b"--units" | b"--report-to" | b"--entry" | b"--boundary" | b"--relax-dir" | b"--cfg" => i += 2,
            w if w.starts_with(b"--") => i += 1,
            _ => return false,
        }
    }
    false
}

/// The package a `run` names: the first word after its options (and their values).
fn run_package(words: &[String]) -> Option<String> {
    let mut i = 0;
    while i < words.len() {
        let w = words[i].as_str();
        match w {
            "--units" | "--report-to" | "--entry" | "--boundary" | "--relax-dir" | "--cfg" => i += 2,
            _ if w.starts_with("--") => i += 1,
            _ => return Some(w.to_string()),
        }
    }
    None
}

/// The package's `[package.metadata.makepad.run-env]` (relax resolve::run_env), for every way it
/// is run (a checkout, the stores, the runner's tiles): set unless the environment already has it.
fn apply_run_env(workspace: &str, package: &str) {
    // Manifest discovery does not evaluate target predicates. Freeze compilation inputs
    // after run-env has been applied.
    let discovery = std::sync::Arc::new(relax_compiler::Session::default());
    let Ok(dir) = relax_compiler::resolve::package_dir(&discovery, workspace, package) else { return };
    let Ok(text) = relax_compiler::vfs::read_to_string(format!("{dir}/Cargo.toml")) else { return };
    for (k, v) in relax_compiler::resolve::run_env(&text) {
        if std::env::var_os(&k).is_none() {
            std::env::set_var(&k, &v);
        }
    }
}

/// Runs `spec`'s package from its repositories' stores (fetched, or the cached commits): mounted
/// on Relax's VFS as a virtual workspace, then the normal run.
fn run_spec(opts: Vec<String>, spec: &fetch::Spec, cached: bool, rest: Vec<String>) -> i32 {
    if rest.first().map_or(true, |p| p.starts_with('-')) {
        eprintln!("relax: run <git url> needs a package after the URL");
        return 2;
    }
    let home = fetch::home();
    // the launcher's report from the start: what the fetch has to say (a remote it could not
    // reach, the stored commit it runs instead) reaches the runner's tile
    if let Some(i) = opts.iter().position(|o| o == "--report-to") {
        if let Some(p) = opts.get(i + 1) {
            let _ = relax_compiler::run::report_open(p);
        }
    }
    let snap = match if cached { fetch::cached(&home, spec) } else { fetch::fetch(&home, spec) } {
        Ok(s) => s,
        Err(e) => {
            eprintln!("relax: {e}");
            return 1;
        }
    };
    let workspace = match fetch::mount(&home, &snap) {
        Ok(w) => w,
        Err(e) => {
            eprintln!("relax: {e}");
            return 1;
        }
    };
    // and the spec itself (the runner names its own repositories for apps that share them)
    std::env::set_var("RELAX_SPEC", spec.args().join("\u{1f}"));
    run_mounted(&workspace, opts, rest)
}

/// `run [options] [--root <folder>] --src <store>[@<offset>+<len>] <package> ...`: the app from a packed source
/// archive (packsrc.rs): the store, or the range of a bigger file it sits in (an APK asset), is the
/// whole workspace; nothing is read from a checkout.
fn run_src(words: &[String]) -> i32 {
    let mut opts = Vec::new();
    let mut src = None;
    let mut root = None;
    let mut i = 0;
    while i < words.len() && words[i].starts_with("--") {
        let n = match words[i].as_str() {
            "--src" => {
                let Some(s) = words.get(i + 1) else {
                    eprintln!("relax: --src wants <store>[@<offset>+<len>]");
                    return 2;
                };
                src = Some(s.clone());
                i += 2;
                continue;
            }
            "--root" => {
                let Some(r) = words.get(i + 1) else {
                    eprintln!("relax: --root wants a folder");
                    return 2;
                };
                root = Some(r.clone());
                i += 2;
                continue;
            }
            "--units" | "--report-to" | "--entry" | "--boundary" | "--relax-dir" | "--cfg" => 2,
            _ => 1,
        };
        opts.extend(words[i..(i + n).min(words.len())].iter().cloned());
        i += n;
    }
    let rest = words[i..].to_vec();
    let Some(src) = src else {
        eprintln!("relax: --src goes before the package");
        return 2;
    };
    if rest.first().map_or(true, |p| p.starts_with('-')) {
        eprintln!("relax: run --src <store> needs a package after the store");
        return 2;
    }
    let (path, range) = match src.rsplit_once('@').and_then(|(p, r)| relax_compiler::vfs::parse_range(r).map(|r| (p, Some(r)))) {
        Some((p, r)) => (p.to_string(), r),
        None => (src.clone(), None),
    };
    let (path, range) = (std::path::Path::new(&path), range);
    let mounted = match range {
        Some((offset, len)) => mount_archive(path, offset, len, root.as_deref()),
        None => std::fs::metadata(path).map_err(|e| format!("{}: {e}", path.display())).and_then(|m| mount_archive(path, 0, m.len(), root.as_deref())),
    };
    match mounted {
        Ok(workspace) => run_mounted(&workspace, opts, rest),
        Err(e) => {
            eprintln!("relax: {e}");
            1
        }
    }
}

/// Mounts the packed source archive (`pack-src`) that sits at `offset`+`len` of `file` (a whole
/// store file, or an APK asset) as the whole workspace and returns the workspace's root: `root`, or
/// one fixed root per home (the compile cache keys a crate by its root path, so a run is warm
/// against the previous one; `--root` puts it where a checkout of the same sources sits).
pub fn mount_archive(file: &std::path::Path, offset: u64, len: u64, root: Option<&str>) -> Result<String, String> {
    let store = relax_compiler::gitstore::Store::open_range(file, offset, len)
        .map_err(|e| format!("{}: {e}", file.display()))?
        .ok_or_else(|| format!("{}: not a Relax git store", file.display()))?;
    let [(commit, _)] = store.index.tables.as_slice() else {
        return Err(format!("{}: a source archive holds exactly one commit", file.display()));
    };
    let commit = *commit;
    let workspace = match root {
        Some(r) => r.trim_end_matches('/').to_string(),
        None => fetch::home().join("vfs").join("src").display().to_string(),
    };
    relax_compiler::vfs::mount(&workspace, std::sync::Arc::new(store), &commit)?;
    Ok(workspace)
}

/// Runs `rest` (the package and its flags) with `opts` (`cmd_run`'s options before the package)
/// in `workspace`, a virtual workspace whose stores are mounted on Relax's VFS. Also the
/// embedder's entry (the Android host mounts the APK's source store, then runs `--exports`).
pub fn run_mounted(workspace: &str, opts: Vec<String>, rest: Vec<String>) -> i32 {
    let workspace = workspace.to_string();
    std::env::set_var("RELAX_WORKSPACE", &workspace);
    // programs it starts that run on Relax (the runner's apps) mount the same repositories
    std::env::set_var("RELAX_VFS", relax_compiler::vfs::mounts_text());
    // Verify the mounted std against the compiler build before any std disk probes.
    let own = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("compiler/std");
    relax_compiler::std_source::select(&workspace, &own);
    // the run's own files (unit graph, build script outputs, code cache): no workspace on disk,
    // so its relax dir is $RELAX_HOME/target/<hash of the virtual workspace> (relax dirs.rs), one
    // per spec shape (the same across updates)
    apply_run_env(&workspace, &rest[0]);
    boot_package(opts, rest)
}

/// Runs `rest` (the package and its flags) with `opts` in the current directory, a checkout:
/// the way `relax run <package>` does, returning instead of exiting (an embedder's call).
pub fn run_checkout(opts: Vec<String>, rest: Vec<String>) -> i32 {
    if let Ok(cwd) = std::env::current_dir() {
        apply_run_env(&cwd.display().to_string(), &rest[0]);
    }
    boot_package(opts, rest)
}

fn boot_package(opts: Vec<String>, rest: Vec<String>) -> i32 {
    provided();
    let mut a = opts;
    a.extend(rest);
    let mut invocation = vec!["loader".to_string(), "run".to_string()];
    invocation.extend_from_slice(&a);
    let sess = relax_compiler::session_from_env(&invocation);
    relax_compiler::run::cmd_run(&sess, &a)
}

/// Per-file identity data emitted by build.rs, parsed only on a mismatch.
fn source_manifest(name: &str) -> &'static [u8] {
    match name {
        "relax_provided_fixture" => include_bytes!(concat!(env!("OUT_DIR"), "/relax-provided-fixture.src.bin")),
        "makepad_live_id" => include_bytes!(concat!(env!("OUT_DIR"), "/makepad-live-id.src.bin")),
        "makepad_script" => include_bytes!(concat!(env!("OUT_DIR"), "/makepad-script.src.bin")),
        "makepad_script_std" => include_bytes!(concat!(env!("OUT_DIR"), "/makepad-script-std.src.bin")),
        "makepad_script_census" => include_bytes!(concat!(env!("OUT_DIR"), "/makepad-script-census.src.bin")),
        "makepad_script_compute" => include_bytes!(concat!(env!("OUT_DIR"), "/makepad-script-compute.src.bin")),
        "makepad_shader" => include_bytes!(concat!(env!("OUT_DIR"), "/makepad-shader.src.bin")),
        "makepad_tween_script" => include_bytes!(concat!(env!("OUT_DIR"), "/makepad-tween-script.src.bin")),
        "makepad_script_audio_aot" => include_bytes!(concat!(env!("OUT_DIR"), "/makepad-script-audio-aot.src.bin")),
        "makepad_hal" => include_bytes!(concat!(env!("OUT_DIR"), "/makepad-hal.src.bin")),
        _ => panic!("unregistered provided crate {name}"),
    }
}

/// The source identity build.rs computed for a provided crate (srchash.rs).
fn src(name: &str) -> u64 {
    let v = match name {
        "relax_provided_fixture" => env!("RELAX_SRC_relax_provided_fixture"),
        "makepad_live_id" => env!("RELAX_SRC_makepad_live_id"),
        "makepad_script" => env!("RELAX_SRC_makepad_script"),
        "makepad_script_std" => env!("RELAX_SRC_makepad_script_std"),
        "makepad_script_census" => env!("RELAX_SRC_makepad_script_census"),
        "makepad_script_compute" => env!("RELAX_SRC_makepad_script_compute"),
        "makepad_shader" => env!("RELAX_SRC_makepad_shader"),
        "makepad_tween_script" => env!("RELAX_SRC_makepad_tween_script"),
        "makepad_script_audio_aot" => env!("RELAX_SRC_makepad_script_audio_aot"),
        "makepad_hal" => env!("RELAX_SRC_makepad_hal"),
        _ => panic!("unknown provided crate: {name}"),
    };
    u64::from_str_radix(v, 16).unwrap()
}

/// The crates built into this binary that Relax binds instead of compiling (provided.rs): their
/// `#[relax_api]` entries, read from this binary's `relax_api` link section.
/// Each binds only while the program's source of it is the one built here (check_sources).
// The provided crates: nothing here calls into them, but they must be in the link for their
// `#[relax_api]` entries (rustc keeps a linked crate's #[used] statics; an unnamed dependency is
// not linked at all)
extern crate makepad_hal;
extern crate makepad_live_id;
extern crate makepad_script;
extern crate makepad_script_audio_aot;
extern crate makepad_script_census;
extern crate makepad_script_compute;
extern crate makepad_script_std;
extern crate makepad_shader;
extern crate makepad_tween_script;
extern crate relax_provided_fixture;

fn provided() {
    use std::collections::HashMap;
    // the HAL starts and stops apps as domains through this host; the boot app's privilege is the host's grant
    hal_host::register();
    if PRIVILEGED.load(std::sync::atomic::Ordering::Relaxed) {
        hal_host::boot_privileged();
    }
    const CRATES: [&str; 10] = [
        "relax_provided_fixture",
        "makepad_live_id",
        "makepad_script",
        "makepad_script_std",
        "makepad_script_census",
        "makepad_script_compute",
        "makepad_shader",
        "makepad_tween_script",
        "makepad_script_audio_aot",
        "makepad_hal",
    ];
    for krate in CRATES {
        let mut shims = HashMap::new();
        let mut types = HashMap::new();
        let mut layouts = HashMap::new();
        for e in makepad_relax_api::entries() {
            if e.module.split("::").next() != Some(krate) {
                continue;
            }
            if e.kind == 0 || e.kind > 4 {
                continue;
            }
            match e.kind {
                makepad_relax_api::OP => {
                    if let Some(f) = e.shim {
                        shims.insert(relax_compiler::provided::norm((e.key)()), relax_compiler::provided::Shim { sig: (e.sig)(), slots: e.slots, f });
                    }
                }
                makepad_relax_api::HANDLE => {
                    types.insert(relax_compiler::provided::norm((e.key)()), (e.size, e.align, e.drop));
                }
                makepad_relax_api::PLAIN => {
                    layouts.insert(relax_compiler::provided::norm((e.key)()), (e.size, e.align, e.offsets));
                }
                _ => {}
            }
        }
        relax_compiler::provided::register(krate, shims, types, layouts, makepad_relax_api::last_panic, src(krate), source_manifest(krate));
    }

    // Splash VM registry -> relax inspect (vm list, script error events)
    relax_compiler::inspect::set_vm_provider(makepad_script::inspect_registry::summaries);
    relax_compiler::inspect::set_script_stack_provider(makepad_script::inspect_registry::script_stack);
    makepad_script::inspect_registry::set_error_hook(relax_compiler::inspect::script_error_event);
}
