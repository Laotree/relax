//! The loader: Relax (relax; makepad's proc macros JIT-compiled by its host, macros.rs
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
mod fetch;
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

fn main() {
    // CEF started this loader as a subprocess of the program it runs (cef.rs)
    if let Some(code) = cef::subprocess() {
        std::process::exit(code);
    }
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
    if std::env::args().nth(1).as_deref() == Some("--version") {
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
    let args: Vec<String> = std::env::args().collect();
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

/// The package a `run` names: the first word after its options (and their values).
fn run_package(words: &[String]) -> Option<String> {
    let mut i = 0;
    while i < words.len() {
        let w = words[i].as_str();
        match w {
            "--units" | "--report-to" | "--entry" | "--boundary" | "--relax-dir" => i += 2,
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
    std::env::set_var("RELAX_WORKSPACE", &workspace);
    // programs it starts that run on Relax (the runner's apps) mount the same repositories
    std::env::set_var("RELAX_VFS", relax_compiler::vfs::mounts_text());
    // and the spec itself (the runner names its own repositories for apps that share them)
    std::env::set_var("RELAX_SPEC", spec.args().join("\u{1f}"));
    // Verify the mounted std against the compiler build before any std disk probes.
    let own = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("compiler/std");
    relax_compiler::std_source::select(&workspace, &own);
    // the run's own files (unit graph, build script outputs, code cache): no workspace on disk,
    // so its relax dir is $RELAX_HOME/target/<hash of the virtual workspace> (relax dirs.rs), one
    // per spec shape (the same across updates)
    apply_run_env(&workspace, &rest[0]);
    provided();
    let mut a = opts;
    a.extend(rest);
    let mut invocation = vec!["loader".to_string(), "run".to_string()];
    invocation.extend_from_slice(&a);
    let sess = relax_compiler::session_from_env(&invocation);
    relax_compiler::run::cmd_run(&sess, &a)
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
    use std::collections::{HashMap, HashSet};
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
        let mut owns = HashSet::new();
        for e in makepad_relax_api::entries() {
            if e.module.split("::").next() != Some(krate) {
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
                makepad_relax_api::OWNS => {
                    owns.insert(relax_compiler::provided::norm((e.key)()));
                }
                _ => {}
            }
        }
        relax_compiler::provided::register(krate, shims, types, layouts, owns, makepad_relax_api::last_panic, src(krate));
    }

    // Splash VM registry -> relax inspect (vm list, script error events)
    relax_compiler::inspect::set_vm_provider(makepad_script::inspect_registry::summaries);
    relax_compiler::inspect::set_script_stack_provider(makepad_script::inspect_registry::script_stack);
    makepad_script::inspect_registry::set_error_hook(relax_compiler::inspect::script_error_event);
}
