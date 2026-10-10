//! `relax run <package> [cargo flags] [-- app args]`: boots a whole cargo package from source
//! inside Relax and runs its `fn main`.
//!
//! Boot: cargo's unit graph for the package (host target, release, features as given), crate
//! substitution (std/substitutes.txt), build scripts (cfgs, link libraries, OUT_DIR,
//! rustc-env), then core/alloc/std (std unless RELAX_STD says otherwise) and every crate in
//! dependency order, import resolution, signatures/layouts, the libraries the build scripts
//! link, and finally `main` through its lazy stub: every function compiles on its first call.
//! With `--ahead` a worker compiles the functions the previous run compiled (recorded per package
//! in <target>/relax/relax-run/<package>.startup, dirs.rs) while the program runs.
//!
//! Options (before the package): `--units <json>` uses a saved unit graph instead of cargo;
//! `--ahead`; `--quiet` (no compile-error stream); `--verbose` (phase timings and info).
//! Env: RELAX_VERBOSE=1, RELAX_STD, RELAX_RUN_ERRORS=N (resolve /
//! signature errors printed, default 20), RELAX_RUN_REPORT=<path> (JSON boot report).
//! `--report-to <path>`: progress for a launcher (the runner app), see `report` below.
//! Errors stay on stderr; verbose adds phases and the exit summary. The program's first-present
//! hook prints its startup line from the RELAX_RUN_* metadata published before main.

macro_rules! eprintln {
    ($($arg:tt)*) => { if !crate::diag::enabled() { std::eprintln!($($arg)*); } };
}

// Callbacks without a session use the verbosity frozen by cmd_run_inner, never the environment.
macro_rules! verbose {
    ($($arg:tt)*) => { if VERBOSE.load(Ordering::Relaxed) { eprintln!($($arg)*); } };
}

use crate::jit::{self, FnKey, Unit};
use crate::program::{DefId, DefKind};
use crate::unitgraph;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::time::Instant;

static mut RUN_UNIT: *mut Unit = std::ptr::null_mut();
static PHASES: std::sync::Mutex<Vec<(String, f64)>> = std::sync::Mutex::new(Vec::new());
static MAIN_START_MS: AtomicU64 = AtomicU64::new(0);
static ERRORS_SEEN: AtomicU64 = AtomicU64::new(0);
static QUIET: AtomicBool = AtomicBool::new(false);
static SILENT: AtomicBool = AtomicBool::new(false);
pub(crate) static VERBOSE: AtomicBool = AtomicBool::new(false);
static STARTUP_PATH: std::sync::Mutex<String> = std::sync::Mutex::new(String::new());
static REPORT_PATH: std::sync::Mutex<String> = std::sync::Mutex::new(String::new());
/// The package's root crate and manifest dir (RELAX_MAIN_COMPILE_LOG's header).
static ROOT_DIR: std::sync::Mutex<String> = std::sync::Mutex::new(String::new());

fn phase(name: &str, t: Instant) {
    let ms = t.elapsed().as_secs_f64() * 1e3;
    if !SILENT.load(Ordering::Relaxed) {
        verbose!("relax-run: {:<28} {:>9.1} ms   (t={:.0} ms)", name, ms, crate::clock::ms_since_start());
    }
    // the phase's name without its counts: "build scripts (12)" -> "build scripts"
    report("phase", name.split(" (").next().unwrap_or(name));
    PHASES.lock().unwrap().push((name.to_string(), ms));
    crate::tui::phase_done(name);
}

// ---- `--report-to <path>`: progress lines for a launcher (the runner app)
//
// Appended to <path> (a file or a FIFO), one event per line, tab-separated, each with the
// milliseconds since Relax started:
//   phase <name> <ms>      a boot phase finished (unit graph, build scripts, load+parse,
//                          resolve, signatures, link libraries, image)
//   main <ms>              boot done, `main` called
//   fns <n> <ms>           functions compiled so far (every 100 ms while it changes)
//   error <text> <ms>      a compile error (newlines and tabs as spaces)
//   panic <text> <ms>      main panicked: kind, message and Relax's crash report
//   exit <code> <ms>       main returned
//   progress <done> <total|-> <label> <ms>   a git store fetch of the launch (progress.rs),
//                          throttled to whole percents
// The program gets RELAX_REPORT_TO=<path>: the makepad platform appends `present` (no time:
// the launcher times every line on receipt) at its first frame on glass. Writes are whole lines with O_APPEND, so the
// writers never interleave within a line.
static REPORT_FILE: std::sync::Mutex<Option<std::fs::File>> = std::sync::Mutex::new(None);

pub fn report_open(path: &str) -> Result<(), String> {
    let f = std::fs::OpenOptions::new().create(true).append(true).open(path).map_err(|e| format!("--report-to {}: {}", path, e))?;
    *REPORT_FILE.lock().unwrap() = Some(f);
    crate::progress::set_report(report);
    unsafe { std::env::set_var("RELAX_REPORT_TO", path) };
    Ok(())
}

pub(crate) fn report(kind: &str, text: &str) {
    use std::io::Write;
    let mut g = REPORT_FILE.lock().unwrap();
    if let Some(f) = g.as_mut() {
        let text: String = text.chars().map(|c| if c == '\n' || c == '\t' || c == '\r' { ' ' } else { c }).collect();
        let _ = f.write_all(format!("{}\t{}\t{:.0}\n", kind, text, crate::clock::ms_since_start()).as_bytes());
    }
}

pub(crate) fn reporting() -> bool {
    REPORT_FILE.lock().unwrap().is_some()
}

extern "C" {
    fn atexit(f: extern "C" fn()) -> i32;
}

fn usage() -> i32 {
    eprintln!("usage: relax run [--units <unit-graph.json>] [--ahead] [--quiet] [--verbose] <package> [cargo flags] [-- program args]");
    2
}

static GANDALF_CONSOLE: std::sync::Mutex<Option<crate::gandalf_out::Console>> = std::sync::Mutex::new(None);

pub fn cmd_run(sess: &std::sync::Arc<crate::Session>, args: &[String]) -> i32 {
    let json = args.iter().any(|a| a == "--json") && args.iter().any(|a| a == "--check");
    let start = std::time::Instant::now();
    if json { crate::diag::enable(); }
    if args.iter().any(|a| a == "--watch") {
        session_cache_off();
    }
    if !args.iter().any(|a| a == "--check") {
        *GANDALF_CONSOLE.lock().unwrap() = Some(crate::gandalf_out::Console::start(crate::diag::enabled(), args.iter().any(|a| a == "--quiet")));
    }
    let code = cmd_run_inner(sess, args, None);
    crate::tui::exit_code(code);
    if let Some(exit) = EXIT_SUMMARY.get() {
        // atexit runs after application TLS destructors. Do not quiesce earlier:
        // those destructors may still call JIT code on the returning main thread.
        let _ = exit.code.set(code);
    } else {
        if let Some(console) = GANDALF_CONSOLE.lock().unwrap().take() { console.detach(); }
        crate::why::event("boundary", "run-exit", 0, "", Some(crate::why::Cause::new("", 0, "exit", &code.to_string())));
    }
    if json && (code != 0 || !args.iter().any(|a| a == "--watch")) {
        if code != 0 && crate::diag::emitted_errors() == 0 {
            crate::diag::emit(&crate::diag::Diagnostic::new("run", "", 0, 0, "check could not load or initialize the package"));
        }
        println!("{{\"type\":\"summary\",\"errors\":{},\"warnings\":0,\"ms\":{}}}", crate::diag::emitted_errors(), start.elapsed().as_millis());
    }
    code
}

/// A warm check session runs with the disk cache off (unless RELAX_CACHE says otherwise): with
/// cached code installed, constant evaluation in a session crashed (makepad-platform's
/// font_policy consts, 2026-10-07) -- to be fixed, then the cache can serve the cold start.
fn session_cache_off() {
    if std::env::var_os("RELAX_CACHE").is_none() {
        unsafe { std::env::set_var("RELAX_CACHE", "off") };
    }
}

/// Load the same front end as `relax check`, transferring ownership to a warm caller.
pub fn load_check_session(sess: &std::sync::Arc<crate::Session>, args: &[String]) -> Result<crate::serve::Session, String> {
    session_cache_off();
    let mut a = vec!["--check".to_string()]; a.extend_from_slice(args);
    let mut session = None;
    let code = cmd_run_inner(sess, &a, Some(&mut session));
    session.ok_or_else(|| format!("check could not load or initialize the package (status {})", code))
}

fn cmd_run_inner(sess: &std::sync::Arc<crate::Session>, args: &[String], session: Option<&mut Option<crate::serve::Session>>) -> i32 {
    crate::clock::mark_process_start();
    jit::begin_startup_phase();
    let mut driver_options = sess.options.clone();
    crate::registry_net::install();
    crate::pmhost::install();
    if let Err(e) = sess.runtime.validate_native_macros() {
        eprintln!("relax-run: {e}");
        return 1;
    }
    jit::COMPILE_ERRORS_FATAL.store(true, Ordering::Relaxed);
    jit::FAULTS_FATAL.store(true, Ordering::Relaxed);
    crate::clock::mark_start();
    let _ = jit::wall_ns();
    let mut units_json = String::new();
    let mut ahead = false;
    let mut entries: Vec<String> = Vec::new();
    let mut check = false;
    let mut watch = session.is_some();
    let mut deep = false;
    let mut boundary: Option<Vec<String>> = None;
    let mut host_gen: Option<(String, String)> = None;
    let mut root_only = false;
    let mut selftest = false;
    let mut i = 0;
    while i < args.len() && args[i].starts_with("--") {
        match args[i].as_str() {
            "--units" if i + 1 < args.len() => {
                units_json = args[i + 1].clone();
                i += 1;
            }
            "--ahead" => ahead = true,
            // `relax selftest --root-only`: the root crate's fns and what they reach
            "--root-only" => root_only = true,
            // `relax selftest` (lib.rs): the check, then every fn compiled (check.rs)
            "--selftest" => selftest = true,
            "--verbose" => driver_options.verbose = true,
            "--report-to" if i + 1 < args.len() => {
                if let Err(e) = report_open(&args[i + 1]) {
                    eprintln!("relax-run: {}", e);
                    return 2;
                }
                i += 1;
            }
            // run these fns (no-argument, by def path) one after another instead of `main`
            "--entry" if i + 1 < args.len() => {
                entries.push(args[i + 1].clone());
                i += 1;
            }
            "--quiet" => QUIET.store(true, Ordering::Relaxed),
            // the parent run's relax dir (dirs.rs): a build script it runs shares it
            "--relax-dir" if i + 1 < args.len() => {
                crate::dirs::set_relax_dir(std::path::PathBuf::from(&args[i + 1]));
                i += 1;
            }
            // nothing of Relax's own on stderr but errors (a program re-running itself)
            "--silent" => {
                QUIET.store(true, Ordering::Relaxed);
                SILENT.store(true, Ordering::Relaxed);
            }
            // type/borrow check (`--deep` also compiles), run nothing
            "--check" => check = true,
            "--watch" => watch = true,
            "--deep" => deep = true,
            "--json" if crate::diag::enabled() => {
                QUIET.store(true, Ordering::Relaxed);
                SILENT.store(true, Ordering::Relaxed);
            },
            // relaxed Rust for every crate of this session (relaxed.rs): all features, or a list
            "--relaxed" => driver_options.relaxed = Some("all".to_string()),
            a if a.starts_with("--relaxed=") => driver_options.relaxed = Some(a[10..].to_string()),
            // with --check: list every site only relaxed mode accepts (what rustc would reject)
            "--strict-report" => crate::relaxed::STRICT_REPORT.store(true, Ordering::Relaxed),
            // `--boundary a,b`: with --check, audit what Relax-compiled code reaches inside
            // crates a, b (boundary.rs)
            "--boundary" => {
                i += 1;
                boundary = args.get(i).map(|s| s.split(',').map(|x| x.to_string()).collect());
            }
            // `--host-gen <crate> <rows>`: with --check, write provided crate <crate>'s shim rows
            // as this run's target sees it (provided.rs; a `relax host-gen` worker)
            "--host-gen" if i + 2 < args.len() => {
                host_gen = Some((args[i + 1].replace('-', "_"), args[i + 2].clone()));
                i += 2;
            }
            _ => return usage(),
        }
        i += 1;
    }
    if i >= args.len() {
        return usage();
    }
    driver_options.verbose &= !SILENT.load(Ordering::Relaxed);
    VERBOSE.store(driver_options.verbose, Ordering::Relaxed);
    if driver_options.verbose { crate::tui::track_for_verbose(); }
    // the boot progress line (tui.rs): a terminal run of a program, with nothing asking for plain output
    unsafe { std::env::remove_var("RELAX_RUN_PROGRESS") };
    if !check && !watch && session.is_none() && entries.is_empty() {
        crate::tui::start(!driver_options.verbose && !QUIET.load(Ordering::Relaxed) && !crate::diag::enabled());
    }
    // `relax run` of a working tree is a live session (watcher + hot reload); sources served from
    // a store (`relax run <git url>`, mounted bundles) are not, and neither are checks and the
    // build scripts / self re-runs a program starts.
    if !check && std::env::var_os("RELAX_SCRIPT_DEPTH").is_none() && !SILENT.load(Ordering::Relaxed)
        && !crate::vfs::is_virtual(&workspace_dir()) {
        driver_options.live = true;
    }
    // a one-shot check compiles every fn of the workspace's crates and all they reach (and
    // --root-only, whose speculative callee builds reach far past the root: Scope ran out at
    // 256k slots): a whole-graph function table, unless RELAX_TABLE_SLOTS says otherwise.
    // 2M slots (Stage reaches 1.41M); the table's thunks and stubs (48 B a slot) share the
    // 768 MB code reservation with the code itself (Stage: 522 MB), so 4M ran it out of code
    if check && !watch && session.is_none() && std::env::var_os("RELAX_TABLE_SLOTS").is_none() {
        driver_options.table_slots = driver_options.table_slots.max(1 << 21);
    }
    let frozen = std::sync::Arc::new(crate::Session { options: driver_options, runtime: sess.runtime.clone() });
    let sess = &frozen;
    let options = &sess.options;
    let runtime = &sess.runtime;
    // edits made in the virtual folders (RELAX_EDITS) against the release this run is: carried
    // over, or kept aside and reported (never dropped); not again inside a build script
    if std::env::var_os("RELAX_SCRIPT_DEPTH").is_none() {
        for c in crate::vfs::reconcile_edits() {
            eprintln!("relax: edit conflict: {c}");
            report("note", &c);
        }
    }
    let package = args[i].clone();
    let mut cargo_flags = Vec::new();
    let mut prog_args: Vec<Vec<u8>> = vec![package.clone().into_bytes()];
    let mut k = i + 1;
    while k < args.len() && args[k] != "--" {
        cargo_flags.push(args[k].clone());
        k += 1;
    }
    if k < args.len() {
        // the program's arguments as given (bytes; `args` is Relax's lossy view)
        let raw: Vec<Vec<u8>> = crate::os::proc::args_bytes();
        if let Some(d) = raw.iter().position(|a| a == b"--") {
            for a in &raw[d + 1..] {
                prog_args.push(a.clone());
            }
        }
    }
    // the program's argv[0] / current_exe() is the Relax binary; spawning it again
    // (`Command::new(env::current_exe()?)`, `Command::new(&args[0])`) runs this program again
    // with the new arguments (std process.rs: RELAX_SELF_EXEC holds this command line up to `--`);
    // a spawn of it with `run` as the first argument launches another program instead
    if let Ok(exe) = std::env::current_exe().and_then(|e| e.canonicalize()) {
        let mut pre: Vec<String> = std::env::args_os().map(|a| a.to_string_lossy().into_owned()).collect();
        if let Some(d) = pre.iter().position(|a| a == "--") {
            pre.truncate(d);
        }
        pre[0] = exe.display().to_string();
        // the re-run is silent: its stderr is the program's (rustc's binary prints nothing else)
        if pre.len() > 1 && !pre.iter().any(|a| a == "--silent") {
            pre.insert(2, "--silent".to_string());
            // an exec replacing this process (makepad-cef's re-exec into its app bundle) is this
            // session going on, not a re-run: it drops the added flag and stays live
            unsafe { std::env::set_var("RELAX_SELF_EXEC_SILENT_ADDED", "1") };
        }
        for j in 1..pre.len() {
            if pre[j - 1] == "--units" && !std::path::Path::new(&pre[j]).is_absolute() {
                pre[j] = format!("{}/{}", workspace_dir(), pre[j]);
            }
        }
        pre.push("--".to_string());
        unsafe { std::env::set_var("RELAX_SELF_EXEC", pre.join("\u{1f}")) };
        prog_args[0] = exe.display().to_string().into_bytes();
    }
    let workspace = workspace_dir();
    // everything this run writes: the workspace's <target>/relax (dirs.rs)
    let target_dir = crate::dirs::relax_dir().display().to_string();
    crate::source_context::set_output_dir(&target_dir);
    // std is the std the program runs on, unless RELAX_STD says otherwise
    if crate::vfs::is_virtual(&workspace) {
        crate::std_source::select(&workspace, std::path::Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/std")));
    }
    if std::env::var_os("RELAX_STD").is_none() {
        let mut d = std::env::current_exe().unwrap_or_default();
        for _ in 0..3 {
            d.pop();
        }
        let mut candidates = vec![format!("{}/tools/relax/compiler/std", workspace), format!("{}/src/tools/relax/compiler/std", d.display())];
        candidates.retain(|c| std::path::Path::new(c).join("std/lib.rs").exists());
        if let Some(c) = candidates.first() {
            std::env::set_var("RELAX_STD", c);
        }
    }
    let std_dir = crate::std_dir();
    if !SILENT.load(Ordering::Relaxed) {
        verbose!("relax-run: package {} ({}), std {}", package, if cargo_flags.is_empty() { "default features".to_string() } else { cargo_flags.join(" ") }, std_dir);
    }

    let mem_g = crate::memstat::tag(crate::memstat::Tag::Boot);
    // ---- crate graph
    let t = Instant::now();
    // the resolver's graph in memory; a build script's child reads its units from JSON
    let units = if units_json.is_empty() {
        unitgraph::unit_graph(sess, &workspace, &package, &cargo_flags)
    } else {
        std::fs::read(&units_json).map_err(|e| format!("{}: {}", units_json, e)).and_then(|d| unitgraph::Units::from_json(&d))
    };
    let units = match units {
        Ok(u) => u,
        Err(e) => {
            eprintln!("relax-run: {}", e);
            return 1;
        }
    };
    let t_load = Instant::now();
    let mut g = match unitgraph::load(&units) {
        Ok(g) => g,
        Err(e) => {
            eprintln!("relax-run: {}", e);
            return 1;
        }
    };
    // provided crates bind only to their own source (before substitution rewrites deps)
    let ts = Instant::now();
    let pkgs: Vec<crate::srchash::SrcPkg> = g
        .crates
        .iter()
        .zip(g.pkg.iter())
        .map(|(c, (dir, name, ver))| crate::srchash::SrcPkg { name: name.clone(), version: ver.clone(), dir: dir.clone(), features: c.features.clone(), deps: c.deps.iter().map(|d| d.0).collect(), proc_macro: c.proc_macro })
        .collect();
    let live_inputs = options.live.then(|| crate::reload::Inputs::collect(&g, &std_dir, &workspace));
    // Validate native macros before any overlapping provided-crate identity error.
    if let Err(e) = crate::crates::apply_substitutes(sess, &mut g.crates, &std_dir) {
        eprintln!("relax-run: crate substitution: {}", e);
        return 1;
    }
    // Shim generation inspects source without executing it, including while bootstrapping.
    if !check || host_gen.is_none() {
        if let Err(e) = crate::provided::check_sources(&pkgs, !options.verbose) {
            eprintln!("relax-run: {}", e);
            return 1;
        }
    }
    phase("provided sources", ts);
    if crate::preload::trace() {
        eprintln!("boot-trace: unit graph (resolve) {:.1} ms, graph {:.1} ms", (t_load - t).as_secs_f64() * 1e3, t_load.elapsed().as_secs_f64() * 1e3);
    }
    phase("unit graph", t);
    let t = Instant::now();
    if let Err(e) = unitgraph::run_build_scripts(sess, &mut g, &target_dir) {
        eprintln!("relax-run: {}", e);
        return 1;
    }
    phase(&format!("build scripts ({})", g.build_scripts.len()), t);
    {
        // the scripts that still run (as Relax programs) that the source is to lose (unitgraph::script_role)
        let mut l = unitgraph::TO_REMOVE.lock().unwrap().clone();
        if !l.is_empty() && !SILENT.load(Ordering::Relaxed) {
            l.sort();
            let names: Vec<String> = l.iter().map(|(p, src)| format!("{} ({})", p, src)).collect();
            verbose!("relax-run: build scripts to remove ({}; only makepad-platform keeps one): {}", l.len(), names.join(", "));
        }
    }

    drop(mem_g);
    let mem_g = crate::memstat::tag(crate::memstat::Tag::Load);
    // fn bodies a later parse can do alone are parsed on their first need (a warm run needs
    // few: their code comes from the disk cache); --check reads every body. RELAX_LAZY_BODIES=0: off
    if !check && options.lazy_bodies {
        crate::parser::LAZY_AUTO.store(true, Ordering::Relaxed);
    }
    // ---- load + parse + collect items, crate by crate in dependency order
    let t = Instant::now();
    let load_profile = crate::load_profile::span(sess.runtime.profile, "load-parse", "main");
    let mut prog = crate::program::Program::new(sess);
    if sess.runtime.parse_verify { let _ = crate::preload::VERIFY.set(crate::front::verify_file); }
    // every crate's cfg set and env!() environment, then all of them scanned and parsed ahead
    // (preload.rs) while the loop below collects them in order
    let order = crate::crates::topo_order(&g.crates);
    let mut cfgs: Vec<crate::cfg::CfgSet> = Vec::with_capacity(g.crates.len());
    for (ci, c) in g.crates.iter().enumerate() {
        let mut cs = crate::cfg::CfgSet::host(sess, &c.features);
        cs.set.push("relax".to_string());
        for x in &g.cfgs[ci] {
            cs.set.push(x.replace('"', ""));
        }
        cfgs.push(cs);
        crate::crates::set_crate_env(&c.name, g.env[ci].clone());
    }
    let mut pre = crate::std_pre_crates(sess);
    let std_count = pre.len();
    let std_names: Vec<_> = pre.iter().map(|c| (c.name.clone(), c.name.clone())).collect();
    let mut pre_index = vec![usize::MAX; g.crates.len()];
    for &ci in &order {
        let c = &g.crates[ci];
        let deps: Vec<_> = c.deps.iter().filter_map(|(d, e)| g.crates.get(*d).map(|x| (e.clone(), x.name.clone()))).collect();
        let mut image_dep_names = std_names.clone();
        image_dep_names.extend(deps.iter().cloned());
        let mut image_deps: Vec<_> = (0..std_count).collect();
        image_deps.extend(c.deps.iter().map(|(d, _)| pre_index[*d]));
        pre_index[ci] = pre.len();
        pre.push(crate::preload::PreCrate { name: c.name.clone(), root: c.src_path.clone(), edition: c.edition, cfg: cfgs[ci].clone(), deps,  proc_macro: c.proc_macro, image_deps, image_dep_names });
    }
    let tp = Instant::now();
    let root_dir = crate::unitgraph::manifest_dir_of(&g.crates[g.root].src_path);
    // the one app-crate rule (borrowck::event): check, serve and run share it
    let app_roots = crate::reload::gandalf_app_roots(&units, &root_dir);
    if crate::borrowck::lazy::gandalf_enabled(options) {
        verbose!("relax-run: gandalf app scope ({} crates): {}", app_roots.len(), app_roots.join(" "));
    }
    crate::borrowck::event::set_app_scope(app_roots);
    let front_images = crate::cache::FrontImages::open(options);
    prog.record_front = front_images.is_some();
    if front_images.is_none() && (crate::preload::trace() || crate::memstat::enabled()) {
        verbose!("relax-front: 0 crates from crate images (0 files, no parse), {} crates parsed", pre.len());
    }
    let verify_collected = std::env::var("RELAX_COLLECTED_VERIFY").is_ok_and(|v| v == "1");
    let mut verification_graph = None;
    let mut collected_tcx = None;
    let mut collected_definitions = None;
    let restored = if check { None } else {
        front_images.as_ref().and_then(|images| images.restore_collected(sess, &pre))
    };
    let restored = if verify_collected {
        verification_graph = restored.filter(|(p, _, _)| p.crates.len() == pre.len());
        if let Some((saved, _, _)) = &verification_graph { prog.seed_collected_symbols(saved); }
        else {
            eprintln!("relax-collected: verification requires a current complete image; run once without RELAX_COLLECTED_VERIFY first");
            return 1;
        }
        None
    } else { restored };
    let restored_crates = restored.as_ref().map_or(0, |(p, _, _)| p.crates.len());
    // std came from the collected image, so this load makes no std parses for the proc-macro
    // world: it parses its own instead of waiting for them (share_std_begin at the graph's
    // registration; load_std_crates_with ends the sharing only when it runs). An app-edit
    // relaunch built the world for the suffix's derives and waited 10 s for every std file.
    if restored_crates != 0 { crate::program::share_std_end(); }
    let collected_restored = restored_crates == pre.len();
    // a load that parses crates expands their macros: the proc-macro world starts building on
    // its own thread now. A warm restore of the whole program expands nothing: no world (the
    // first live edit that expands builds it).
    if !collected_restored {
        if let Err(e) = crate::macro_reg::prewarm(sess) {
            eprintln!("relax-run: {e}");
            return 1;
        }
    }
    // the whole program came from the collected store: it holds this program already
    COLLECTED_CURRENT.store(collected_restored, Ordering::Relaxed);
    let collected_suffix = restored.as_ref().filter(|_| !collected_restored)
        .map(|(p, _, _)| (p.defs.len(), p.imports.len()));
    let mut cold_front = crate::cache::ColdFront::default();
    let mut crate_of = vec![u32::MAX; g.crates.len()];
    let mut load_errors = 0;
    let mut watch_load_errors = Vec::new();
    let core;
    if let Some((restored_prog, restored_tcx, definitions)) = restored {
        prog = restored_prog;
        for &ci in &order { if pre_index[ci] < restored_crates { crate_of[ci] = pre_index[ci] as u32; } }
        collected_tcx = Some(restored_tcx);
        collected_definitions = definitions;
    }
    if collected_restored {
        core = prog.prelude_crate.expect("collected graph prelude");
    } else {
        let recipe = crate::crate_image::GraphRecipe::new(&pre);
        let replay = (restored_crates != 0).then(|| pre.clone());
        let mut remaining: Vec<_> = pre.into_iter().skip(restored_crates).collect();
        for c in &mut remaining {
            c.image_deps = c.image_deps.iter().filter_map(|d| d.checked_sub(restored_crates)).collect();
        }
        // A partial restore has already checked selection against the complete
        // graph. Continue that plan and its contexts, not a new suffix closure.
        let plan = prog.demand_plan.take();
        prog.preload_images_bounded(remaining, front_images.as_ref().map(|x| x as &dyn crate::crate_image::CrateImages), crate::cache::ColdFront::enabled(options) && mem_budget_mode(), plan);
        if let Some(replay) = replay {
            prog.front_graph = Some(recipe);
            // Replay uses the full graph, not the suffix's rebased image indices.
            prog.load_recipe = replay;
        }
        let (loaded_core, std_deps) = if restored_crates == 0 {
            match crate::load_std_crates_with(sess, &mut prog, |p, k| cold_front.loaded(p, k)) {
                Ok(x) => x,
                Err(e) => { eprintln!("relax-run: std: {}", e); return 1; }
            }
        } else {
            (prog.prelude_crate.expect("collected graph prelude"),
                (0..std_count).map(|k| (prog.crates[k].name, k as u32)).collect())
        };
        core = loaded_core;
        crate::tui::LOAD_TOTAL.store(order.len() as u32, Ordering::Relaxed);
        for &ci in &order {
            crate::tui::LOAD_DONE.fetch_add(1, Ordering::Relaxed);
            if pre_index[ci] < restored_crates { continue; }
            let c = &g.crates[ci];
            crate::tui::crate_begin(&c.name);
            let mut deps = std_deps.clone();
            for (d, n) in &c.deps {
                if crate_of[*d] != u32::MAX {
                    deps.push((prog.syms.intern(n), crate_of[*d]));
                }
            }
            match prog.load_crate_deferred(&c.name, &c.src_path, c.edition, cfgs[ci].clone(), deps) {
                Ok(kk) => {
                    prog.crates[kk as usize].proc_macro = c.proc_macro;
                    crate_of[ci] = kk;
                    cold_front.loaded(&mut prog, kk);

                }
                Err(e) => {
                    if watch {
                        // A syntax error at startup must still leave an editable session. The
                        // loader has already allocated this crate's root module. Give an
                        // unparsed root an empty AST until its first valid editor version.
                        let krate = prog.crates.len() as u32 - 1;
                        crate_of[ci] = krate;
                        let module = prog.crates[krate as usize].root_mod;
                        if !prog.file_paths.iter().any(|p| crate::vfs::normalize_path(p) == crate::vfs::normalize_path(&c.src_path)) {
                            if let Ok(pf) = crate::parser::parse_owned(sess, Vec::new(), c.edition) {
                                if let Ok(file) = prog.add_generated_file(&c.src_path, pf, krate, module) {
                                    prog.set_mod_file(module, file);
                                    let d = prog.mods[module as usize].def;
                                    prog.set_def_file(d, file);
                                }
                            }
                        }
                        let d = crate::diag::from_legacy(&e, "parse");
                        watch_load_errors.push(crate::diag::record(e.clone(), d));
                    } else if crate::diag::enabled() { crate::diag::emit(&crate::diag::from_legacy(&e, "parse")); }
                    eprintln!("relax-run: load error {}: {}", c.name, e);
                    load_errors += 1;
                }
            }
        }
        if load_errors == 0 { cold_front.finish(&mut prog); }
        cold_front.report(&prog);
        if load_errors == 0 {
            // All preload workers have joined. Each crate now owns its lowering
            // context exclusively; retain its source identities and validation ledger,
            // not the compiler's already-consumed lowering intermediates.
            // A context still shared (another owner kept a clone) keeps its state.
            let _release = crate::load_profile::span(sess.runtime.profile, "front-context-release", "main");
            for c in &mut prog.crates {
                if let Some(cx) = std::sync::Arc::get_mut(&mut c.context) { cx.finish_load(); }
            }
        }
    }
    let preload_ms = tp.elapsed().as_secs_f64() * 1e3;
    prog.prelude_crate = Some(core);
    let lines = prog.lines_loaded;
    let again = crate::program::PARSE_AGAIN.load(std::sync::atomic::Ordering::Relaxed);
    let again = if again > 0 { format!(", {} parsed again", again) } else { String::new() };
    crate::tui::crate_end();
    phase(&format!("load+parse ({} crates, {} files, {}k lines{})", g.crates.len(), prog.files.len(), lines / 1000, again), t);
    drop(load_profile);
    if sess.runtime.profile { crate::load_profile::flush(); }
    if crate::preload::trace() {
        let ext: usize = prog.files.iter().map(|f| f.src.len() - f.src_len as usize).sum();
        let toks: usize = prog.files.iter().map(|f| f.toks.len()).sum();
        eprintln!("boot-trace: expansion text {} KB, tokens {}k", ext >> 10, toks >> 10);
    }
    let tf = Instant::now();
    crate::pmhost::flush_cache();
    if crate::preload::trace() {
        eprintln!("boot-trace: proc-macro world cache flush {:.1} ms; {}", tf.elapsed().as_secs_f64() * 1e3, crate::pmhost::cache_line());
    }
    // the program's files are loaded: the macro world goes (hot reload or a run-time module
    // builds it again from its disk cache)
    let pm0 = crate::memstat::live_of(crate::memstat::Tag::PmHost);
    let freed = crate::pmhost::free_world();
    crate::native_macros::report(sess.runtime.profile);
    if crate::preload::trace() && crate::memstat::enabled() {
        eprintln!("boot-trace: pmhost heap {} KB before the free, {} KB after", pm0 >> 10, crate::memstat::live_of(crate::memstat::Tag::PmHost) >> 10);
    }
    if freed {
        // its heap goes back to the system (freed chunks otherwise stay resident, scattered
        // between the program's allocations: ~70 MB on counter), off the boot path
        let trace = crate::preload::trace();
        std::thread::spawn(move || {
            let (r0, t) = (if trace { crate::memstat::resident() } else { 0 }, Instant::now());
            crate::memstat::trim();
            if trace {
                eprintln!("boot-trace: macro world heap trimmed: rss {} -> {} MB in {:.1} ms", r0 >> 20, crate::memstat::resident() >> 20, t.elapsed().as_secs_f64() * 1e3);
            }
        });
    }
    if crate::preload::trace() {
        eprintln!("boot-trace: preload (scan) {:.1} ms; loader waited {:.1} ms for parses; parse cpu {:.1} ms; publish (under the pool lock) {:.1} ms", preload_ms, crate::preload::WAIT_NS.load(Ordering::Relaxed) as f64 / 1e6, crate::preload::PARSE_NS.load(Ordering::Relaxed) as f64 / 1e6, crate::preload::PUBLISH_NS.load(Ordering::Relaxed) as f64 / 1e6);
        eprintln!("boot-trace: macro scopes {:.1} ms; relaxed settings {:.1} ms", crate::macros::SCOPE_NS.load(Ordering::Relaxed) as f64 / 1e6, crate::relaxed::FEATURES_NS.load(Ordering::Relaxed) as f64 / 1e6);
        let ph: Vec<f64> = crate::preload::PHASE_NS.iter().map(|x| x.load(Ordering::Relaxed) as f64 / 1e6).collect();
        eprintln!("boot-trace: parse cpu split: fn bodies {:.0} ms, derives {:.0} ms, macro_rules transcription {:.0} ms, format family {:.0} ms, other built-in / hosted fn-like macros {:.0} ms", ph[0], ph[1], ph[2], ph[3], ph[4]);
        let hs = crate::macro_reg::stats();
        if hs.calls + hs.failed > 0 {
            eprintln!("boot-trace: proc-macro host: world {:.1} ms (built on its own thread), {} expansions {:.1} ms wall summed (JIT compile {} fns {:.1} ms CPU, encode {:.1} ms, decode {:.1} ms), {} failed", hs.world_ns as f64 / 1e6, hs.calls, hs.call_ns as f64 / 1e6, hs.compiled, hs.compile_ns as f64 / 1e6, hs.encode_ns as f64 / 1e6, hs.decode_ns as f64 / 1e6, hs.failed);
            let ph: Vec<f64> = crate::pmhost::PH.iter().map(|x| x.load(Ordering::Relaxed) as f64 / 1e6).collect();
            eprintln!("boot-trace: proc-macro host phases (summed): lookup {:.1} ms, call {:.1} ms, stats {:.1} ms", ph[0], ph[1], ph[2]);
            let tl = crate::pmhost::timeline();
            eprintln!("boot-trace: proc-macro host timeline: world build started t={:.0} ms, ready t={:.0} ms; first expansion asked t={:.0} ms; waits for the world {} ({:.0} ms summed); first call returned t={:.0} ms", tl[0], tl[1], tl[2], tl[4] as u64, tl[5], tl[3]);
        }
        let mut v = crate::preload::BY_NAME.lock().unwrap().clone();
        v.sort_by_key(|e| std::cmp::Reverse(e.2));
        for e in v.iter().take(12) {
            eprintln!("boot-trace:   {}! {} calls {:.1} ms", e.0, e.1, e.2 as f64 / 1e6);
        }
    }
    // a failed derive leaves its generated items out of the program (rustc would reject it):
    // never silent; --check counts them as errors
    let derive_failures = crate::macro_reg::derive_failures();
    if !derive_failures.is_empty() {
        eprintln!("relax-run: derive failures: {} (their generated items are missing)", derive_failures.len());
        for m in derive_failures.iter().take(std::env::var("RELAX_RUN_ERRORS").ok().and_then(|v| v.parse().ok()).unwrap_or(20)) {
            eprintln!("  {}", m);
        }
    }
    if load_errors > 0 && !watch {
        return 1;
    }
    let root = crate_of[g.root];
    if root == u32::MAX {
        eprintln!("relax-run: the package root did not load");
        return 1;
    }

    drop(mem_g);
    let mem_g = crate::memstat::tag(crate::memstat::Tag::Resolve);
    // ---- resolve
    let t = Instant::now();
    if let Some((first, imports)) = collected_suffix { prog.resolve_imports_added(imports, first); }
    else if !collected_restored { prog.resolve_imports(); }
    if runtime.lazy_verify {
        if let Err(error) = prog.verify_lazy(crate::front::verify_file) {
            eprintln!("{error}");
            return 1;
        }
    }
    phase("resolve", t);
    // C0 (relax-cache.md): crate fingerprints + build id, computed and reported only
    if std::env::var_os("RELAX_CACHE_FP").is_some() {
        crate::stable::report_fingerprints(&prog);
        if std::env::var("RELAX_CACHE_FP").map_or(false, |v| v == "features") {
            return 0;
        }
    }
    let max_err: usize = std::env::var("RELAX_RUN_ERRORS").ok().and_then(|v| v.parse().ok()).unwrap_or(20);
    if !prog.errors.is_empty() {
        eprintln!("relax-run: {} unresolved imports (first {}):", prog.errors.len(), max_err.min(prog.errors.len()));
        for e in prog.errors.iter().take(max_err) {
            eprintln!("  {}", e);
        }
    }

    drop(mem_g);
    let mem_g = crate::memstat::tag(crate::memstat::Tag::Sigs);
    // ---- signatures, layouts, impl tables
    let t = Instant::now();
    let mut tcx = collected_tcx.take().unwrap_or_else(crate::tcx::Tcx::new);
    // RELAX_PERTURB: type ids shift (code must not depend on them; syms.rs reloc_sig)
    for i in 0..crate::syms::perturb(options) {
        let u8_ = tcx.tys.prim(crate::program::Prim::U8);
        let _ = tcx.tys.intern(crate::types::TyKind::Array(u8_, tcx.tys.const_usize(1000 + i)));
    }
    *ROOT_DIR.lock().unwrap() = format!("{} {}", g.crates[g.root].name, root_dir);
    crate::program::collect_misses_begin();
    if let Some((first, _)) = collected_suffix { tcx.collect_collected_suffix(&prog, first); }
    else if !collected_restored { tcx.collect_declarations(&prog); }
    // A signature, field or impl header that names a type in a file the lazy selection skipped
    // (a closure miss): load those files and collect again, until nothing is missing.
    let mut deferred_errors: Vec<String> = Vec::new();
    loop {
        let mods = prog.misses_to_load(&crate::program::collect_misses_take());
        if mods.is_empty() { break; }
        if std::env::var_os("RELAX_DEFERRED_TRACE").is_some() {
            eprintln!("relax-deferred: signatures name types in {} skipped file(s): loaded before main", mods.len());
        }
        let (f0, d0) = (prog.files.len() as u32, prog.defs.len());
        for m in mods {
            if let Err(e) = prog.load_deferred_module(m) {
                eprintln!("relax: loading a deferred module failed: {}", e);
                deferred_errors.push(format!("loading a deferred module failed: {}", e));
            }
        }
        prog.link_deferred_modules(f0, d0);
        tcx = crate::tcx::Tcx::new();
        crate::program::collect_misses_begin();
        tcx.collect_declarations(&prog);
    }
    phase("signatures", t);
    if !tcx.errors.is_empty() {
        eprintln!("relax-run: {} signature errors (first {}):", tcx.errors.len(), max_err.min(tcx.errors.len()));
        for e in tcx.errors.iter().take(max_err) {
            eprintln!("  {}", e);
        }
    }

    if check {
        // a check runs no program: a constant that cannot be evaluated is a reported error
        // (E0080), as for `relax test` / `live`, not the end of the process
        jit::COMPILE_ERRORS_FATAL.store(false, Ordering::Relaxed);
        crate::jit::compile_watch(Some(("check: own errors", 0)));
        let mut pre = crate::macro_reg::derive_failures();
        pre.extend(watch_load_errors);
        // the watch session reports its root crate's; a one-shot check every workspace crate's
        let checked = if watch || root_only || session.is_some() { vec![root] } else if selftest { crate::check::workspace_crates(&prog, root) } else { crate::check::app_crates(&prog, root) };
        // A run checks coherence in the background; a check needs its errors now: the app
        // check its own crates' impls (cargo check), every other check all of them.
        let t = Instant::now();
        if selftest || watch || root_only || session.is_some() { tcx.check_coherence(&prog); }
        else { tcx.check_coherence_of(&prog, Some(&checked)); }
        phase("coherence", t);
        for k in checked {
            pre.extend(crate::check::own_errors(&prog, k, &prog.errors, "resolve"));
            pre.extend(crate::check::own_errors(&prog, k, &tcx.errors, "typeck"));
        }
        if let Some((name, out)) = &host_gen {
            let Some(k) = prog.crates.iter().position(|c| prog.syms.str(c.name) == name.as_str()) else {
                eprintln!("relax-run: --host-gen: no crate `{}` in the graph", name);
                return 2;
            };
            // A table is only as complete as the read behind it: a failed derive drops the
            // items it generates, an unresolved import or a signature error drops what names
            // it, and the crate reads as smaller without failing. Any such error fails the
            // worker (`relax host-gen` then writes nothing), never a short table.
            let mut gaps: Vec<String> = crate::macro_reg::derive_failures();
            gaps.extend(deferred_errors.iter().cloned());
            gaps.extend(prog.errors.iter().map(|e| format!("resolve: {e}")));
            gaps.extend(tcx.errors.iter().map(|e| format!("signature: {e}")));
            if !gaps.is_empty() {
                eprintln!("relax host-gen: {} ({}): {} error(s) reading the crate graph; no shim rows (first {}):", name, sess.options.target, gaps.len(), max_err.min(gaps.len()));
                for g in gaps.iter().take(max_err) {
                    eprintln!("  {}", g);
                }
                return 1;
            }
            let errors = tcx.dcx.clone();
            // the crate's reviewed interface (relax_api.txt), passed by `relax host-gen`
            let api = match std::env::var("RELAX_HOST_API").ok().and_then(|f| std::fs::read_to_string(f).ok()) {
                Some(t) => match crate::provided::HostApi::parse(&t) {
                    Ok(a) => a,
                    Err(e) => {
                        eprintln!("relax host-gen: {e}");
                        return 1;
                    }
                },
                None => crate::provided::HostApi::default(),
            };
            let (rows, rep) = match crate::provided::host_gen(&prog, &tcx, k as u32, &api) {
                Ok(r) => r,
                Err(e) => {
                    eprintln!("relax host-gen: {e}");
                    return 1;
                }
            };
            let text = crate::provided::rows_to_text(&rows);
            errors.flush_delayed();
            let (errors, warnings) = errors.drain_reported();
            for warning in warnings { eprintln!("warning: {}", warning.message); }
            if !errors.is_empty() {
                for error in errors { eprintln!("{}", error.message); }
                return 1;
            }
            if let Err(e) = std::fs::write(out, text) {
                eprintln!("relax-run: --host-gen: {}: {}", out, e);
                return 2;
            }
            eprintln!("{}", rep);
            return 0;
        }
        crate::jit::compile_watch(Some(("check: unit", 0)));
        let t = Instant::now();
        let mut u = Unit::new(prog, tcx, core);
        phase("unit", t);
        // every body is checked, so the files the selection skipped load first: all of them for
        // selftest, a watch session or --root-only; the checked (app) crates' for the app check
        let t = Instant::now();
        if selftest || watch || root_only || session.is_some() {
            unsafe { jit::load_all_skipped(&mut *u) };
        } else {
            let crates = crate::check::app_crates(&u.prog, root);
            unsafe { jit::load_skipped_of(&mut *u, &crates) };
        }
        phase("load checked files", t);
        crate::jit::compile_watch(Some(("check: crate", 0)));
        if let Some(b) = &boundary {
            if let Err(e) = crate::boundary::start(&u, b) {
                eprintln!("relax-run: {}", e);
                return 2;
            }
            // the audit lowers every fn of every crate: a constant that cannot be evaluated is one
            // failed row, not the end of the run
            jit::COMPILE_ERRORS_FATAL.store(false, Ordering::Relaxed);
            let rep = crate::boundary::run(&mut *u);
            print!("{}", rep);
            std::mem::forget(u);
            return 0;
        }
        if let Some(out) = session {
            *out = Some(crate::serve::Session::new(u, root, pre));
            return 0;
        }
        // the warm session (type + borrow check; --deep also compiles); a one-shot `relax
        // check` keeps compiling everything, as the gates that use it expect
        if watch {
            let mut session = crate::serve::Session::new(u, root, pre);
            return session.watch(deep);
        }
        let code = crate::check::check_crate(&mut u, root, pre, root_only, selftest);
        // the parsed files go to the cache's front images as a run's do (one store shared with
        // `relax run`): the next check (or run) of the package maps them instead of parsing
        // every file again (Stage: 6 s of a warm check was parsing)
        if !selftest { record_check_front(&mut u, options); }
        if crate::memstat::enabled() {
            crate::memstat::print("check complete", &crate::memreport::unit_sizes(&u));
        }
        std::mem::forget(u);
        return code;
    }

    // ---- main
    let main_def = match find_main(&prog, root) {
        Some(d) => d,
        None => {
            eprintln!("relax-run: no `fn main` at the root of {}", g.crates[g.root].name);
            return 1;
        }
    };
    let mut entry_defs = Vec::new();
    for e in &entries {
        let mut found = None;
        for (di, d) in prog.defs.iter().enumerate() {
            if matches!(d.kind, DefKind::Fn | DefKind::AssocFn) && prog.def_path(DefId(di as u32)) == *e {
                found = Some(DefId(di as u32));
            }
        }
        match found {
            Some(d) => entry_defs.push(d),
            None => {
                eprintln!("relax-run: --entry `{}`: no such fn", e);
                return 1;
            }
        }
    }

    // ---- the libraries the build scripts link (#[link] blocks load on the first miss)
    let t = Instant::now();
    let mut missing = Vec::new();
    for (name, fw) in &g.link_libs {
        if !crate::os::proc::load_library(name, *fw) && (*fw || !crate::os::proc::load_library_versioned(name)) {
            missing.push(name.clone());
        }
    }
    // what the system linker would have linked: every library an active extern block names
    // with #[link] (frameworks register their Objective-C classes and protocols on load, and
    // the program looks those up by name at run time)
    let mut n_link = g.link_libs.len();
    for (name, fw) in link_attr_libs(&prog) {
        if g.link_libs.iter().any(|l| l.0 == name && l.1 == fw) {
            continue;
        }
        n_link += 1;
        if !crate::os::proc::load_library(&name, fw) && (fw || !crate::os::proc::load_library_versioned(&name)) {
            missing.push(name);
        }
    }
    phase(&format!("link libraries ({})", n_link), t);
    // a library that is not there only matters when one of its symbols is used: that miss is
    // reported where it happens (the #[link] block's lazy load); here only with --verbose
    if !missing.is_empty() {
        verbose!("relax-run: libraries not found: {:?}", missing);
    }

    let t = Instant::now();
    let fn_defs = if ahead { startup_defs(&prog, &format!("{}/relax-run/{}.startup", target_dir, package)) } else { Vec::new() };
    let root_crate = prog.def(main_def).krate;
    crate::layout::set_root_crate(root_crate);
    // A live session (hot reload of the program's own sources, reload.rs); set
    // before anything is laid out (app structs take the live layout, layout.rs live_editable)
    if options.live {
        crate::layout::LIVE_SESSION.store(true, Ordering::Relaxed);
    }
    let mut u = Unit::new(prog, tcx, core);
    if let Some((saved_prog, saved_tcx, _)) = verification_graph {
        saved_prog.verify_collected(&u.prog);
        saved_tcx.verify_collected(&saved_prog, &u.prog, &u.tcx);
        eprintln!("relax-collected: verified restored graph against rebuilt graph");
    }
    let enum_errors = u.tcx.check_enum_discriminants(&u.prog, root_crate);
    if !enum_errors.is_empty() {
        for error in enum_errors { eprintln!("error: {}", error); }
        return 1;
    }
    jit::set_program_args(prog_args);
    jit::start_background_coherence(&u);
    drop(mem_g);
    let mem_g = crate::memstat::tag(crate::memstat::Tag::CacheLoad);
    // Classify the disk cache before workers add newly compiled entries.
    // a warm start: every crate's pack accepted, every front image restored, and the startup
    // slot manifest an earlier run recorded still names entries of this cache
    let mut warm_start = None;
    unsafe { std::env::set_var("RELAX_RUN_CACHE", "off") };
    // a fully restored collected program keeps the boot file count it was recorded with
    if !collected_restored { u.prog.boot_files = u.prog.files.len(); }
    if let Some(mode) = crate::cache::mode_from_env(options) {
        match crate::cache::Cache::open_collected(&u, mode, collected_definitions.as_ref()) {
            Ok(mut c) => {
                c.load_manifest(root_crate);
                let warm = c.startup_manifest_valid() && c.stats.packs_rejected == 0 && c.stats.packs as usize == u.prog.crates.len() && (!u.prog.record_front || u.prog.front_restored.iter().all(|r| *r));
                crate::warm::classify(warm);
                u.front.warm_cache.store(warm, Ordering::Relaxed);
                if warm {
                    warm_start = Some((c.manifest.len(), c.manifest_present, c.manifest_uncached));
                } else if c.has_startup_manifest() && c.manifest_missing > 0 {
                    verbose!("relax-cache: startup manifest stale: {} of its {} slots' entries are gone", c.manifest_missing, c.manifest.len());
                }
                verbose!("relax-cache: {:?}, {} packs ({} rejected), {} code stores, {} entries, opened in {:.1} ms (interfaces {:.1} ms)", mode, c.stats.packs, c.stats.packs_rejected, c.stats.code_stores, c.stats.index_entries, c.stats.open_ns as f64 / 1e6, c.stats.iface_ns as f64 / 1e6);
                // warm: this program ran with this cache before (its startup manifest, recorded
                // after an earlier run reached main); entries other processes of this launch wrote
                // (build scripts, the proc-macro host) do not make a first run warm
                unsafe { std::env::set_var("RELAX_RUN_CACHE", if c.has_startup_manifest() { "warm" } else { "cold" }) };
                u.cache = Some(Box::new(crate::cache::CacheCell::new(c)));
            }
            Err(e) => eprintln!("relax-cache: off ({})", e),
        }
    }
    // files whose front image is in their crate's store: their arrays become slices of it
    // (front.rs), before any worker reads them
    if crate::front::enabled() {
        if let Some(c) = u.cache.as_ref() {
            let prog = &mut u.prog;
            let paths = &prog.file_paths;
            let crates_cfg: Vec<&crate::cfg::CfgSet> = prog.file_crate.iter().map(|&k| &prog.crates[k as usize].cfg).collect();
            crate::program::without_std_shares(&mut prog.files, paths, |files| for i in 0..files.len() {
                // Boot images already use a pinned mapping (and were verified at load). Do
                // not fault the same front pages into the cache-open mapping a second time.
                if files[i].src.is_mapped() { continue; }
                let Some(path) = paths.get(i) else { continue };
                let source_hash = files[i].source_hash(path);
                if let Some(img) = c.front_image(path, source_hash) {
                    // a file another holder still shares keeps its heap arrays
                    match std::sync::Arc::get_mut(&mut files[i]) {
                        Some(pf) => {
                            if !crate::front::apply(path, pf, img) { continue; }
                            let cfg = crates_cfg.get(i).copied();
                            if let (Some(pimg), Some(cfg)) = (c.front_part_image(path, source_hash), cfg) {
                                crate::front::apply_part(path, pf, pimg, cfg, false);
                            }
                        }
                        None => {
                            crate::front::SHARED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        }
                    }
                }
            });
        }
    }
    phase("image", t);
    drop(mem_g);
    *STARTUP_PATH.lock().unwrap() = format!("{}/relax-run/{}.startup", target_dir, package);
    if let Ok(p) = std::env::var("RELAX_RUN_REPORT") {
        *REPORT_PATH.lock().unwrap() = p;
    }
    if crate::why::enabled() {
        for (i, d) in u.prog.defs.iter().enumerate() {
            if u.prog.files.get(d.file as usize).and_then(|f| f.ast.items.get(d.item.0 as usize)).is_some() {
                let c = u.prog.why_def(crate::program::DefId(i as u32), "declaration");
                crate::why::event("item-decl", &c.file, c.line, &c.symbol, None);
            }
            if matches!(d.kind, crate::program::DefKind::Fn | crate::program::DefKind::AssocFn) {
                let c = u.prog.why_def(crate::program::DefId(i as u32), "declaration");
                crate::why::event("fn-decl", &c.file, c.line, &c.symbol, None);
            }
        }
    }
    let id = {
        let _why = crate::why::enabled().then(|| {
            let mut c = u.prog.why_def(main_def, "entry-point");
            c.symbol = "run main stub before execution".into();
            crate::why::enter(c)
        });
        u.fn_id(FnKey::Inst(main_def, Vec::new()))
    };
    let entry = u.entry(id);
    let up: *mut Unit = &mut *u;
    unsafe { RUN_UNIT = up };
    start_exit_summary();
    *RUN_DIAGNOSTICS.lock().unwrap() = Some(u.tcx.dcx.clone());
    unsafe { atexit(at_exit) };
    crate::jit::set_exit_hook(at_exit);
    start_monitor(runtime, options);
    // RELAX_MEM_AT_MS=n[,m..]: the memory report (RELAX_MEM_REPORT=1) n ms after main starts,
    // without ending the run's summary (programs that never reach their exit summary: Stage)
    if let Ok(v) = std::env::var("RELAX_MEM_AT_MS") {
        let mem_at_trim = runtime.mem_at_trim;
        let at: Vec<u64> = v.split(',').filter_map(|x| x.trim().parse().ok()).collect();
        std::thread::spawn(move || {
            let t0 = std::time::Instant::now();
            for ms in at {
                let d = std::time::Duration::from_millis(ms).saturating_sub(t0.elapsed());
                std::thread::sleep(d);
                let up = unsafe { RUN_UNIT };
                if up.is_null() || !crate::memstat::enabled() {
                    continue;
                }
                crate::owner::call(crate::owner::Class::App, || {
                    crate::memstat::print(&format!("at {} ms", ms), &crate::memreport::unit_sizes(unsafe { &*up }));
                });
                // RELAX_MEM_AT_TRIM=1: the allocator's free pages back to the system, then the report
                // again (how much of the footprint is freed-but-held memory a trim can return)
                if mem_at_trim {
                    let t = std::time::Instant::now();
                    crate::memstat::trim();
                    let ns = t.elapsed().as_secs_f64() * 1e3;
                    crate::owner::call(crate::owner::Class::App, || {
                        crate::memstat::print(&format!("at {} ms after a {:.1} ms trim", ms, ns), &crate::memreport::unit_sizes(unsafe { &*up }));
                    });
                }
            }
        });
    }
    // RELAX_STATS_AFTER_MS=n: print the compile totals and timeline n ms after boot (programs
    // that never exit: the counter's event loop)
    if let Some(ms) = std::env::var("RELAX_STATS_AFTER_MS").ok().and_then(|v| v.parse::<u64>().ok()) {
        std::thread::spawn(move || {
            std::thread::sleep(std::time::Duration::from_millis(ms));
            crate::owner::call(crate::owner::Class::App, || summary("stats"));
        });
    }
    jit::enable_pipelining(options);
    jit::MAIN_TID.store(jit::current_thread_id(), Ordering::Relaxed);
    // the startup manifest: the slots installed before the first present and in the first 5 s
    // (the next run's workers link the later ones ahead)
    jit::ORDER_UNTIL_NS.store(jit::wall_ns() + 5_000_000_000, Ordering::Relaxed);
    // the manifest's slots before the first present: installed now, from its prelinked image
    let t_pre = Instant::now();
    if unsafe { jit::prelink_startup(up) } > 0 {
        if let Some(c) = unsafe { (*up).cache.as_ref() } {
            let s = &c.stats;
            let ms = |ns: u64| ns as f64 / 1e6;
            verbose!("relax-cache: prelinked {} startup slots and {} data objects in {:.1} ms (image read {:.1}, keys {:.1}, symbols {:.1}, placed+linked+installed {:.1}; {} left lazy: {} stale, {} unresolved, {} had code)", s.prelinked, s.prelink_data, t_pre.elapsed().as_secs_f64() * 1e3,
                ms(s.prelink_parse_ns), ms(s.prelink_keys_ns), ms(s.prelink_syms_ns), ms(s.prelink_ns.saturating_sub(s.prelink_parse_ns + s.prelink_keys_ns + s.prelink_syms_ns)),
                s.prelink_changed + s.prelink_failed + s.prelink_had_code, s.prelink_changed, s.prelink_failed, s.prelink_had_code);
        }
    }
    unsafe { jit::spec_seed_manifest(up) };
    if let Some((n, present, uncached)) = warm_start {
        verbose!("relax-run: warm start, startup manifest of {} slots ({} before the first present, {} without cached code)", n, present, uncached);
    }
    crate::mainprof::start();
    MAIN_START_WALL.store(jit::wall_ns(), Ordering::Relaxed);
    if ahead {
        start_ahead(up, fn_defs);
    }
    // a live session: hot reload of the program's own sources (reload.rs); none for store sources
    if crate::layout::LIVE_SESSION.load(Ordering::Relaxed) {
        crate::reload::start_watcher(up, live_inputs.unwrap_or_default());
    }
    jit::start_completion(up, runtime);
    jit::live_needs_present(u.prog.crates.iter().any(|c| u.prog.syms.str(c.name) == "makepad_platform"));
    jit::startup_main(runtime);
    crate::fncost::mark("boot done, calling main");
    let main_ms = crate::clock::ms_since_start();
    MAIN_START_MS.store(main_ms as u64, Ordering::Relaxed);
    crate::tui::compiling();
    unsafe {
        std::env::set_var("RELAX_RUN_STARTUP_T0", crate::clock::process_start_epoch().to_string());
        std::env::set_var("RELAX_RUN_MAIN_MS", crate::clock::ms_since_process_start().to_string());
        if SILENT.load(Ordering::Relaxed) {
            std::env::remove_var("RELAX_RUN_PACKAGE");
        } else {
            std::env::set_var("RELAX_RUN_PACKAGE", &package);
        }
    }
    if !SILENT.load(Ordering::Relaxed) {
        verbose!("relax-run: boot done, calling main (t={:.0} ms)", main_ms);
    }
    report("main", "");
    if crate::memstat::enabled() {
        crate::memstat::print("boot", &crate::memreport::unit_sizes(&u));
        let l: Vec<u64> = crate::parser::LAZY_STATS.iter().map(|x| x.load(Ordering::Relaxed)).collect();
        for (k, why) in crate::parser::LAZY_WHY.iter().enumerate() {
            if l[k * 2] > 0 {
                eprintln!("relax-mem: fn bodies parsed at load, {}: {} bodies, {} MB parse working set", why, l[k * 2], l[k * 2 + 1] >> 20);
            }
        }
        let mut ms: Vec<(String, u64)> = crate::parser::LAZY_MACROS.lock().unwrap().iter().map(|(k, v)| (k.clone(), *v)).collect();
        ms.sort_by_key(|x| std::cmp::Reverse(x.1));
        if !ms.is_empty() {
            eprintln!("relax-mem: macros keeping bodies eager: {}", ms.iter().take(15).map(|(k, v)| format!("{} {}", k, v)).collect::<Vec<_>>().join(", "));
        }
    }
    if runtime.profile {
        for extension in ["rs"] {
            let suffix = format!(".{extension}");
            let mut eager = 0usize;
            let mut deferred = 0usize;
            let mut parsed = 0usize;
            let mut body_files = 0usize;
            let mut files = std::collections::BTreeSet::new();
            for (path, file) in u.prog.file_paths.iter().zip(&u.prog.files) {
                if !path.ends_with(&suffix) { continue; }
                files.insert(path);
                for item in &file.ast.items {
                    if let crate::ast::ItemKind::Fn(sig, body, _) = item.kind {
                        eager += usize::from(body.is_some());
                        deferred += usize::from(file.ast.fn_sig(sig).lazy_body.is_some());
                    }
                }
                let bodies: usize = file.parts().map(|part| part.bodies.len()).sum();
                parsed += bodies;
                body_files += usize::from(bodies != 0);
            }
            eprintln!("source-file-demand: language={extension} unique_parsed={}", files.len());
            eprintln!("source-body-demand: language={extension} eager={eager} deferred={deferred} parsed_deferred={parsed} deferred_body_files={body_files}");
        }
    }
    // RELAX_BOOT_ONLY=1: stop here (boot timing / profiling)
    if runtime.boot_only && std::env::var_os("RELAX_BUILD_SCRIPT").is_none() {
        crate::why::event("boundary", "boot-done-before-main", 0, "", Some(crate::why::Cause::new("", 0, "boot-only", "application main has not run")));
        std::process::exit(0);
    }
    for (k, d) in entry_defs.iter().enumerate() {
        // speculative workers may be compiling (they add slots): the unit lock around fn_id
        let en = crate::owner::call(crate::owner::Class::App, || {
            let id = u.fn_id(FnKey::Inst(*d, Vec::new()));
            u.entry(id)
        });
        let r = unsafe { jit::call_jit(up, en, 0) };
        flush_errors(true);
        match r {
            Ok(v) => verbose!("relax-run: entry {} returned {:#x} (t={:.0} ms)", entries[k], v, crate::clock::ms_since_start()),
            Err(p) => {
                let rep = crate::owner::call(crate::owner::Class::App, || u.report(&p));
                eprintln!("relax-run: entry {} {}: {}\n  report: {}", entries[k], p.kind, p.message, rep);
            }
        }
    }
    if !entry_defs.is_empty() {
        std::mem::forget(u);
        return 0;
    }
    // `fn main() -> T` (T != ()): rustc's lang_start runs `main().report()` (Termination) and exits
    // with its code; std::process::__relax_lang_start::<T>(main) does the same.
    // (a `#[no_main]` crate's `extern "C" fn main(argc, argv) -> c_int` is called as before)
    let main_ret = u.tcx.fn_sig(&u.prog, main_def).filter(|s| !s.header.abi.is_c_like()).map(|s| s.ret);
    let r = match main_ret {
        Some(ret) if ret != u.tcx.tys.unit => {
            let start = (0..u.prog.defs.len() as u32)
                .map(DefId)
                // std::process re-exports its OS half (`pub use imp::*`: process_unix.rs /
                // process_windows.rs), so the fn's own path is std::process::imp::...
                .find(|d| {
                    u.prog.def(*d).kind == DefKind::Fn
                        && matches!(u.prog.def_path(*d).as_str(), "std::process::__relax_lang_start" | "std::process::imp::__relax_lang_start")
                });
            match start {
                Some(sd) => {
                    let sid = u.fn_id(FnKey::Inst(sd, vec![ret]));
                    let sentry = u.entry(sid);
                    unsafe { jit::call_jit(up, sentry, entry) }
                }
                None => {
                    eprintln!("relax-run: `fn main` returns a value but std has no process::__relax_lang_start");
                    // Workers already hold this unit's pointer. Its Drop waits
                    // for the front end and O3; process shutdown owns it now.
                    std::mem::forget(u);
                    return 1;
                }
            }
        }
        _ => unsafe { jit::call_jit(up, entry, 0) },
    };
    let code = match r {
        Ok(_) => 0,
        Err(p) => {
            // The message now, on this thread (it needs no compiler state): a panic is
            // never silent, whatever the exit's cleanup gets to. Its report (backtrace
            // under the unit lock) is the cleanup worker's, after the compilers stopped.
            eprintln!("relax-run: main {}: {}", p.kind, p.message);
            let _ = RUN_PANIC.set(p);
            101
        }
    };
    // threads the program spawned may still run (and compile) until the process exits, as
    // under rustc where returning from main exits with detached threads still running: the
    // unit must outlive cmd_run (dropping it here freed it under them)
    std::mem::forget(u);
    code
}

/// (name, framework) of every `#[link(name = .., kind = ..)]` on an extern block whose items
/// are active (got definitions), or an empty link-only block without a cfg.
fn link_attr_libs(prog: &crate::program::Program) -> Vec<(String, bool)> {
    let mut out: Vec<(String, bool)> = Vec::new();
    for (fi, f) in prog.files.iter().enumerate() {
        let Some(cfg) = prog.file_crate.get(fi).and_then(|&k| prog.crates.get(k as usize)).map(|c| &c.cfg) else { continue };
        let src = crate::cfg::Src { src: &f.src, toks: &f.toks, ext: &[], ptoks: &[], parts: None };
        // Every item of the file's arena, as before: it also holds the items of macro expansions
        // the collector dropped (libc's cfg_if! branches for other targets carry no #[cfg] of
        // their own), so an empty `#[link] extern "C" {}` of another target's branch still
        // reaches here (root, network, bsd, rt); the collector would have to record the extern
        // blocks it keeps to tell them apart. The `cfg(..)` of `#[link(.., cfg(..))]` is honoured.
        for it in &f.ast.items {
            let active = match &it.kind {
                // an extern block without items: its own #[cfg]s decide, as for any item
                crate::ast::ItemKind::ForeignMod(_, items) if items.is_empty() => crate::cfg::active(src, f.ast.list(it.attrs), cfg),
                crate::ast::ItemKind::ForeignMod(_, items) => f.ast.list(*items).iter().any(|si| prog.item_defs.contains_key(&(fi as u32, si.0))),
                _ => false,
            };
            if !active {
                continue;
            }
            for a in crate::cfg::expand_cfg_attr_list(src, f.ast.list(it.attrs), cfg) {
                if a.toks.hi <= a.toks.lo || f.tok_text(a.toks.lo) != "link" {
                    continue;
                }
                let mut name = String::new();
                let mut fw = false;
                let mut holds = true;
                let mut k = a.toks.lo;
                while k + 2 < a.toks.hi {
                    if f.tok_text(k + 1) == "=" {
                        let v = f.tok_text(k + 2).trim_matches('"').to_string();
                        match f.tok_text(k) {
                            "name" => name = v,
                            "kind" => fw = v == "framework",
                            _ => {}
                        }
                    } else if f.tok_text(k) == "cfg" && f.tok_text(k + 1) == "(" {
                        // `#[link(name = "x", cfg(pred))]` (link_cfg): the library only when
                        // the predicate holds (libc's crt-static variants)
                        let mut depth = 0;
                        let mut end = k + 1;
                        while end < a.toks.hi {
                            match f.tok_text(end) { "(" => depth += 1, ")" => { depth -= 1; if depth == 0 { break; } } _ => {} }
                            end += 1;
                        }
                        holds &= crate::cfg::eval_tokens(src, k as usize + 2, end as usize, cfg);
                        k = end;
                        continue;
                    }
                    k += 1;
                }
                if std::env::var_os("RELAX_LINK_TRACE").is_some() {
                    let item_attrs: Vec<String> = f.ast.list(it.attrs).iter().map(|x| (x.toks.lo..x.toks.hi).map(|t| f.tok_text(t)).collect::<Vec<_>>().join(" ")).collect();
                    eprintln!("relax-link: {} holds={} in {} (item attrs {:?})", name, holds, prog.file_paths[fi], item_attrs);
                }
                if holds && !name.is_empty() && !out.iter().any(|l| l.0 == name && l.1 == fw) {
                    out.push((name, fw));
                }
            }
        }
    }
    out
}

/// The shortest `lib<name>.so.<N>` in the usual library dirs.
/// `fn main` at the root of crate `root`.
/// `main` as rustc's resolver finds it (rustc_resolve lib.rs: `main` resolved in the crate root's
/// value namespace, imports and globs included -- `pub use app::*;` brings it in), then entry.rs:
/// it must be a fn.
fn find_main(prog: &crate::program::Program, root: u32) -> Option<DefId> {
    let sym = prog.syms.get("main")?;
    let m = prog.crates[root as usize].root_mod;
    let d = prog.lookup_in_module(m, sym, false, &mut Vec::new())?;
    if prog.def(d).kind == DefKind::Fn {
        Some(d)
    } else {
        None
    }
}

/// Non-generic fns listed (by def path) in the previous run's startup file, in order.
fn startup_defs(prog: &crate::program::Program, path: &str) -> Vec<DefId> {
    let list = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(_) => return Vec::new(),
    };
    let mut by_path = std::collections::HashMap::new();
    for (i, d) in prog.defs.iter().enumerate() {
        if matches!(d.kind, DefKind::Fn | DefKind::AssocFn) {
            by_path.insert(prog.def_path(DefId(i as u32)), DefId(i as u32));
        }
    }
    let mut out = Vec::new();
    for l in list.lines() {
        if let Some(d) = by_path.get(l.trim()) {
            out.push(*d);
        }
    }
    out
}

/// Ahead-of-call compilation on a worker: the previous run's startup functions, in order.
/// Compiles serialize with lazy compiles on the unit lock, so the worker overlaps with the
/// program's own execution, not with its compiles.
fn start_ahead(up: *mut Unit, defs: Vec<DefId>) {
    let upn = up as usize;
    std::thread::spawn(move || {
        let up = upn as *mut Unit;
        let t = Instant::now();
        let mut n = 0;
        for d in defs {
            let _job = jit::compile_job();
            let (id, done) = crate::owner::call(crate::owner::Class::App, || {
                let id = unsafe { (&mut *up).fn_id(FnKey::Inst(d, Vec::new())) };
                let done = unsafe { (&*up).fns[id as usize].compiled };
                (id, done)
            });
            if !done {
                let _origin = crate::clock::origin("fncost-ahead");
                unsafe { jit::compile_slot(up, id) };
                n += 1;
            }
        }
        verbose!("relax-run: ahead worker compiled {} fns in {:.0} ms (t={:.0} ms)", n, t.elapsed().as_secs_f64() * 1e3, crate::clock::ms_since_start());
    });
}

/// Prints new compile errors as they happen (each failed fn panics only if it is called).
fn flush_errors(block: bool) {
    let up = unsafe { RUN_UNIT };
    if up.is_null() {
        return;
    }
    let body = || {
        let u = unsafe { &mut *up };
        u.flush_query_errors(false);
        let seen = ERRORS_SEEN.load(Ordering::Relaxed) as usize;
        if !QUIET.load(Ordering::Relaxed) {
            for e in u.errors.iter().skip(seen) {
                eprintln!("relax-run: [t={:.0} ms] {}", crate::clock::ms_since_start(), e);
            }
        }
        // the report file may be a FIFO a slow reader drains: written after the unit lock is free
        let to_report: Vec<String> = if u.errors.len() > seen && reporting() { u.errors.iter().skip(seen).map(|e| e.to_string()).collect() } else { Vec::new() };
        ERRORS_SEEN.store(u.errors.len() as u64, Ordering::Relaxed);
        to_report
    };
    let to_report = if block {
        crate::owner::call(crate::owner::program_class(), body)
    } else {
        match crate::owner::call_within(crate::owner::Class::Background, 0, body) {
            Some(r) => r,
            None => return,
        }
    };
    for e in to_report {
        report("error", &e);
    }

}

/// Writes the disk cache's recorded entries once RELAX_CACHE_SPILL_MB (default 16; 0 = only at
/// exit) of them are pending: taken under the unit lock (only if it is free now), written
/// without it. A cold Stage run held ~200 MB of recorded code until the exit flush.
fn spill_cache() {
    static LIM: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    let lim = *LIM.get_or_init(|| std::env::var("RELAX_CACHE_SPILL_MB").ok().and_then(|v| v.parse::<usize>().ok()).unwrap_or(16) << 20);
    let up = unsafe { RUN_UNIT };
    if lim == 0 || up.is_null() {
        return;
    }
    let Some(spill) = crate::owner::call_within(crate::owner::Class::Background, 0, || {
        let u = unsafe { &mut *up };
        match u.cache.as_mut() {
            Some(c) if c.pending_bytes() >= lim => c.spill_take(),
            _ => None,
        }
    }) else { return };
    if let Some(s) = spill {
        // its own thread: the monitor loop's other duties (errors, trims) do not wait for the disk
        std::thread::spawn(move || {
            let t = Instant::now();
            let r = s.write();
            if !VERBOSE.load(Ordering::Relaxed) {
                if let Err(e) = &r { eprintln!("relax-cache: spill: {}", e); }
            }
            if crate::memstat::enabled() || crate::preload::trace() {
                verbose!("relax-cache: spilled {:?} entries in {:.1} ms at t={:.0} ms", r, t.elapsed().as_secs_f64() * 1e3, crate::clock::ms_since_start());
            }
        });
    }
}

static SETTLE_REQUESTED: AtomicBool = AtomicBool::new(false);
static FIRST_PRESENT_WALL: AtomicU64 = AtomicU64::new(0);
static PRESENT_PATH: std::sync::Mutex<Option<std::path::PathBuf>> = std::sync::Mutex::new(None);

/// Observe the platform's existing `present\n` report, independently of whether a launcher
/// requested progress. Only this small report goes through the private rendezvous; progress
/// still goes directly to the launcher (which may be a FIFO).
fn present_report() -> std::io::Result<std::fs::File> {
    let path = std::env::temp_dir().join(format!("relax-present-{}-{}", std::process::id(), jit::wall_ns()));
    let file = std::fs::OpenOptions::new().read(true).write(true).create_new(true).open(&path)?;
    *PRESENT_PATH.lock().unwrap() = Some(path.clone());
    unsafe { std::env::set_var("RELAX_REPORT_TO", path); }
    Ok(file)
}

fn remove_present_report() {
    if let Some(path) = PRESENT_PATH.lock().unwrap().take() {
        let _ = std::fs::remove_file(path);
    }
}

/// Embedders may signal that boot has settled before the automatic quiet detector fires.
/// Nonblocking and safe from a JIT callback / CTFE: the monitor performs the drops outside
/// compilation, retrying until the unit and front locks are available. RELAX_SETTLE_DROP=0
/// disables explicit requests too. This applies to the unit launched by run::cmd_run.
pub fn settle() {
    SETTLE_REQUESTED.store(true, Ordering::Release);
}

#[derive(Default)]
struct SettleWatch {
    seen: Option<u64>,
    quiet_since: u64,
    settled: Option<u64>,
}

impl SettleWatch {
    fn ready(&mut self, now: u64, first_present: u64, compiled: u64) -> bool {
        if self.seen != Some(compiled) {
            self.seen = Some(compiled);
            self.quiet_since = now;
        }
        first_present != 0 && now.saturating_sub(first_present.max(self.quiet_since)) >= 1_000_000_000
            && self.settled != Some(compiled)
    }
}

/// A successful settle takes pending cache entries even below the normal spill threshold.
/// Disk IO and allocator relief run off the monitor and never hold the unit/front locks.
fn try_settle(compiled: u64, drops: &mut jit::SettleDrops, trim: bool) -> bool {
    let up = unsafe { RUN_UNIT };
    if up.is_null() { return false; }
    let Some(Some((drops, pending, spill, at, landmark))) = crate::owner::call_within(crate::owner::Class::Background, 0, || {
        if jit::COMPILED_FNS.load(Ordering::Relaxed) != compiled {
            return None;
        }
        // Immediate releases must be reported even when an ahead checker kept FRONT_RW busy.
        let completed = jit::take_completed_drops();
        drops.fns += completed.fns;
        drops.rir += completed.rir;
        drops.typeck += completed.typeck;
        let drops = std::mem::take(drops);
        let u = unsafe { &mut *up };
        let pending = u.cache.as_ref().map_or(0, |c| c.pending_bytes());
        let spill = u.cache.as_mut().and_then(|c| c.spill_take());
        let at = crate::clock::ms_since_start();
        let present = FIRST_PRESENT_WALL.load(Ordering::Acquire);
        let landmark = if present == 0 { "before first present".to_owned() } else {
            format!("first present +{:.0} ms", jit::wall_ns().saturating_sub(present) as f64 / 1e6)
        };
        Some((drops, pending, spill, at, landmark))
    }) else { return false };
    std::thread::spawn(move || {
        let result = spill.map(|s| s.write());
        // Borrowck already releases its body-owned queries at each completed check.
        let before = crate::memstat::process_rss();
        let trim_start = Instant::now();
        if trim { crate::memstat::trim(); }
        let trim_ms = trim_start.elapsed().as_secs_f64() * 1e3;
        let after = crate::memstat::process_rss();
        if crate::memstat::enabled() || crate::preload::trace() {
            let mb = |n: u64| n as f64 / 1048576.0;
            eprintln!("relax-mem: settle at t={:.0} ms ({}): completed-body drops RIR of {} fns ({:.1} MB), typeck {:.1} MB, lower {:.1} MB, spec {:.1} MB (max sweep {:.1} ms), cache spill {:.1} MB ({:?}); trim{} rss {:.1} -> {:.1} MB in {:.1} ms; before [{}], after [{}]{}",
                at, landmark, drops.fns, mb(drops.rir), mb(drops.typeck), mb(drops.lower), mb(drops.spec),
                drops.max_sweep_ns as f64 / 1e6, mb(pending as u64), result, if trim { "" } else { " disabled" }, mb(before.0), mb(after.0), trim_ms, before.2, after.2,
                if crate::memstat::enabled() { "" } else { " (RIR estimated; other heap bytes require RELAX_MEM_REPORT)" });
        }
    });
    true
}

fn start_monitor(runtime: &crate::options::RuntimeOptions, options: &crate::options::Options) {
    let present_forward = std::env::var_os("RELAX_REPORT_TO");
    let mut present = match present_report() {
        Ok(file) => Some(file),
        Err(e) => { eprintln!("relax-run: first-present report: {}", e); None }
    };
    let runtime = runtime.clone();
    let options = options.clone();
    std::thread::spawn(move || {
        let runtime = &runtime;
        let options = &options;
        // A measurement harness requests an allocator snapshot at its own landmark
        // (for example first present + 20 s), before it reads smaps and stops the app.
        let mut mem_snapshot = std::env::var_os("RELAX_MEM_SNAPSHOT").map(std::path::PathBuf::from);
        let mut last = u64::MAX;
        let settle_on = runtime.settle_drop;
        let mut settle_watch = SettleWatch::default();
        let mut drops = jit::SettleDrops::default();
        let mut reclaimed = None;
        let mut reclaim_requested = false;
        let mut present_bytes = Vec::new();
        let (mut quiet, mut seen, mut trimmed) = (0u32, 0u64, 0u64);
        // growth relief (below): the resident size after the last trim and when it ran
        let (mut grown_from, mut grown_at) = (0u64, std::time::Instant::now().checked_sub(std::time::Duration::from_millis(500)).unwrap_or_else(std::time::Instant::now));
        // mid-run cache writes once main ran 3 s and something new was compiled: after 2 s without
        // compiles (5 s after the last write), or every 10 s while compiles go on
        // (RELAX_CACHE_MID=0: off)
        let mid_on = std::env::var("RELAX_CACHE_MID").map_or(true, |v| v != "0");
        let (mut mid_quiet, mut mid_seen, mut mid_flushed, mut mid_last) = (0u32, u64::MAX, 0u64, 0u64);
        let mid_busy = std::sync::Arc::new(AtomicBool::new(false));
        let mut teardown_started = false;
        loop {
            std::thread::sleep(std::time::Duration::from_millis(100));
            if let Some(file) = present.as_mut() {
                use std::io::{Read, Write};
                let _ = file.read_to_end(&mut present_bytes);
                if present_bytes.windows(8).any(|b| b == b"present\n") {
                    FIRST_PRESENT_WALL.store(jit::wall_ns(), Ordering::Release);
                    present = None;
                    remove_present_report();
                    // Forward the unchanged protocol line, off the rendering thread.
                    if let Some(file) = REPORT_FILE.lock().unwrap().as_mut() {
                        let _ = file.write_all(b"present\n");
                    } else if let Some(path) = &present_forward {
                        if let Ok(mut file) = std::fs::OpenOptions::new().append(true).open(path) {
                            let _ = file.write_all(b"present\n");
                        }
                    }
                }
            }
            if let Some(path) = &mem_snapshot {
                if path.exists() {
                    let mut report = crate::memstat::report("harness snapshot");
                    // structure sizes too (who holds the tags' bytes), when accounting is on
                    let up = unsafe { RUN_UNIT };
                    if crate::memstat::enabled() && !up.is_null() {
                        crate::owner::call(crate::owner::Class::App, || {
                            for (k, v) in crate::memreport::unit_sizes(unsafe { &*up }) {
                                report.push_str(&format!("relax-mem: harness snapshot:   size {:<40} {:>9.1} MB\n", k, v as f64 / 1048576.0));
                            }
                        });
                    }
                    let _ = std::fs::write(path.with_extension("report"), report);
                    mem_snapshot = None;
                }
            }
            if mid_on {
                let n = jit::COMPILED_FNS.load(Ordering::Relaxed) + jit::TIER1_INSTALLS.load(Ordering::Relaxed);
                if n != mid_seen {
                    mid_seen = n;
                    mid_quiet = 0;
                } else {
                    mid_quiet += 1;
                }
                let main_ms = (jit::wall_ns().saturating_sub(MAIN_START_WALL.load(Ordering::Relaxed))) / 1_000_000;
                let start = MAIN_START_WALL.load(Ordering::Relaxed);
                let since = main_ms.saturating_sub(mid_last);
                // also with no new code: the manifest whose window closed, the collected program
                let left = !MID_MANIFEST_DONE.load(Ordering::Relaxed) && jit::FIRST_PRESENT.load(Ordering::Acquire) && jit::wall_ns() >= jit::ORDER_UNTIL_NS.load(Ordering::Relaxed)
                    || !COLLECTED_CURRENT.load(Ordering::Relaxed) && !MID_COLLECTED_TRIED.load(Ordering::Relaxed)
                    || jit::FIRST_PRESENT.load(Ordering::Acquire) && crate::cache::front_graph_pending();
                // the warm record (manifest, front graph, collected program) is written as soon
                // as its pieces are ready after the first present, not after seconds of quiet
                // (a cold run compiles O2 code for long after it): users close apps quickly, and
                // a killed run that wrote nothing left every relaunch unrestored. At most once a
                // second; the collected program's encode takes the unit lock only when free.
                let record = left && jit::FIRST_PRESENT.load(Ordering::Acquire) && since >= 1_000;
                let due = n != mid_flushed && ((mid_quiet >= 20 && since >= 5_000) || since >= 10_000) || left && mid_quiet >= 20 && since >= 5_000;
                if start != 0 && (record || main_ms >= 3000 && due) && !mid_busy.swap(true, Ordering::SeqCst) {
                    mid_flushed = n;
                    mid_last = main_ms;
                    let busy = mid_busy.clone();
                    let quiet = record || mid_quiet >= 20;
                    let _ = std::thread::Builder::new().name("relax-cache-write".to_string()).spawn(move || {
                        let _mem = crate::memstat::tag(crate::memstat::Tag::CacheStore);
                        let t = Instant::now();
                        let r = mid_flush(quiet, record);
                        if crate::memstat::enabled() || std::env::var_os("RELAX_CACHE_TRACE").is_some() {
                            verbose!("relax-cache: mid-run write at t={:.0} ms: {:?} (entries, front images) in {:.1} ms", crate::clock::ms_since_start(), r, t.elapsed().as_secs_f64() * 1e3);
                        }
                        busy.store(false, Ordering::SeqCst);
                    });
                }
            }
            // the program's teardown is built ahead once the first frame has been up for 1 s
            // (jit::prepare_teardown): a quit then runs it instead of compiling it
            let presented = jit::FIRST_PRESENT_NS.load(Ordering::Acquire);
            if !teardown_started && presented != 0 && jit::wall_ns().saturating_sub(presented) >= 1_000_000_000 {
                teardown_started = true;
                let up = unsafe { RUN_UNIT };
                if !up.is_null() {
                    unsafe { jit::prepare_teardown(up) };
                }
            }
            let _job = jit::compile_job();
            jit::reassert_signals();
            flush_errors(false);
            if settle_on {
                let requested = SETTLE_REQUESTED.swap(false, Ordering::AcqRel);
                reclaim_requested |= requested;
                let compiled = jit::COMPILED_FNS.load(Ordering::Relaxed);
                let n = jit::reclaim_generation();
                // Installations release their own finished bodies. Shared inline/template
                // inputs stay through the startup frame: evicting them earlier just makes
                // subsequent startup callers rebuild them. After present, retry shared
                // reclamation as compilation progresses, without a global quiet gate.
                let settled_d = if (FIRST_PRESENT_WALL.load(Ordering::Acquire) != 0 || reclaim_requested)
                    && (reclaimed != Some(n) || reclaim_requested) {
                    crate::owner::call_within(crate::owner::Class::Background, 0, || unsafe { jit::settle_drop(RUN_UNIT) })
                } else { None };
                if let Some(mut d) = settled_d {
                    d.release_rir();
                    drops.fns += d.fns;
                    drops.rir += d.rir;
                    drops.typeck += d.typeck;
                    drops.lower += d.lower;
                    drops.spec += d.spec;
                    drops.max_sweep_ns = drops.max_sweep_ns.max(d.max_sweep_ns);
                    if d.fns != 0 || !d.front_pending || d.typeck != 0 || d.lower != 0 || d.spec != 0 {
                        // A reader may finish after the last installation was trimmed.
                        // Re-arm allocator relief for pages released at this boundary.
                        quiet = 0;
                        trimmed = u64::MAX;
                    }
                    if !d.front_pending {
                        reclaimed = Some(n);
                        reclaim_requested = false;
                    }
                }
                let quiet = settle_watch.ready(jit::wall_ns(), FIRST_PRESENT_WALL.load(Ordering::Acquire), compiled);
                if quiet || requested {
                    if try_settle(compiled, &mut drops, runtime.mem_trim) {
                        settle_watch.settled = Some(compiled);
                    } else if requested {
                        SETTLE_REQUESTED.store(true, Ordering::Release);
                    }
                }
            }
            // speculative results nobody called within the TTL go (memory: jit::expire_spec)
            jit::expire_spec(options);
            // recorded disk-cache entries are written out as they pile up, not held to the exit
            spill_cache();
            // Independent allocator relief for later O3 bursts and non-GUI programs.
            // After 1 s without new compiles (O1 or O3), the malloc allocator's free
            // pages go back to the system, once per compile burst: compile working sets (O3
            // register allocation of a big fn holds 100s of MB for a moment) otherwise stay
            // resident as free-but-held heap (counter warm, x64: 10 s RSS 1,050 -> 892 MB;
            // 2-5 ms on this thread). RELAX_MEM_TRIM=0: off.
            // Growth relief while compiles go on (cold main -> first present never goes quiet for
            // the trim below): the loader's freed parse memory and earlier compile working sets
            // stay in the malloc arenas of the threads that freed them, where other threads'
            // allocations cannot reuse them, so a cold run's footprint adds them up. Whenever the
            // resident size grew RELAX_MEM_TRIM_GROWTH_MB (256) since the last trim -- the first
            // check is at main start, right after the load -- and at most every 500 ms, the free
            // pages go back to the system (Calculator cold, 165: 350 MB at main start in 23 ms).
            if runtime.mem_trim && grown_at.elapsed() >= std::time::Duration::from_millis(500) {
                static STEP: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
                let step = *STEP.get_or_init(|| std::env::var("RELAX_MEM_TRIM_GROWTH_MB").ok().and_then(|v| v.parse().ok()).unwrap_or(256u64)) << 20;
                let rss = crate::memstat::resident();
                if step > 0 && rss >= grown_from + step {
                    let t = Instant::now();
                    crate::memstat::trim();
                    let after = crate::memstat::resident();
                    if crate::memstat::enabled() || crate::preload::trace() {
                        eprintln!("relax-mem: growth trim at t={:.0} ms: rss {} -> {} MB in {:.1} ms", crate::clock::ms_since_start(), rss >> 20, after >> 20, t.elapsed().as_secs_f64() * 1e3);
                    }
                    grown_from = after;
                    grown_at = std::time::Instant::now();
                } else if rss < grown_from {
                    grown_from = rss;
                }
            }
            if runtime.mem_trim {
                let n = if FIRST_PRESENT_WALL.load(Ordering::Acquire) != 0 {
                    jit::reclaim_generation()
                } else {
                    jit::COMPILED_FNS.load(Ordering::Relaxed) + jit::TIER1_INSTALLS.load(Ordering::Relaxed)
                };
                if n != seen {
                    seen = n;
                    quiet = 0;
                } else {
                    quiet += 1;
                    if quiet == 10 && n != trimmed {
                        trimmed = n;
                        let show = crate::memstat::enabled() || crate::preload::trace();
                        let r0 = if show { crate::memstat::resident() } else { 0 };
                        let t = Instant::now();
                        crate::memstat::trim();
                        if show {
                            let r1 = crate::memstat::resident();
                            eprintln!("relax-mem: trim at t={:.0} ms: rss {} -> {} MB in {:.1} ms", crate::clock::ms_since_start(), r0 >> 20, r1 >> 20, t.elapsed().as_secs_f64() * 1e3);
                        }
                    }
                }
            }
            // compile progress, read without the unit lock (it may be held for a while)
            let n = jit::COMPILED_FNS.load(Ordering::Relaxed);
            if n != last && reporting() {
                last = n;
                report("fns", &n.to_string());
            }
        }
    });
}

static RUN_DIAGNOSTICS: std::sync::Mutex<Option<relax_types::infer::diagnostics::DiagCtxt>> = std::sync::Mutex::new(None);

extern "C" fn at_exit() {
    finish_run("exit", EXIT_SUMMARY.get().and_then(|exit| exit.code.get().copied()));
}

struct ExitSummary {
    request: std::sync::mpsc::SyncSender<(&'static str, Option<i32>)>,
    worker: std::thread::JoinHandle<()>,
    code: std::sync::OnceLock<i32>,
}
static EXIT_SUMMARY: std::sync::OnceLock<ExitSummary> = std::sync::OnceLock::new();
static RUN_PANIC: std::sync::OnceLock<jit::PanicInfo> = std::sync::OnceLock::new();
/// The exit worker has not finished the cache write yet (finish_run waits for it).
static EXIT_PERSIST: AtomicBool = AtomicBool::new(false);
/// How long the exit waits for background compiles to release the unit (they are abandoned
/// at their next safe point). Not getting it means no cache write at all.
const EXIT_QUIESCE_MS: u64 = 200;
/// The thread ending the process holds the unit lock itself (a program error in a build or
/// a link called exit): its compile is half done, the exit worker can never get the lock, and
/// waiting for it would only delay the exit.
static EXIT_CALLER_HOLDS: AtomicBool = AtomicBool::new(false);
fn exit_quiesce_ms() -> u64 {
    if EXIT_CALLER_HOLDS.load(Ordering::SeqCst) { 0 } else { EXIT_QUIESCE_MS }
}

fn start_exit_summary() {
    let (request, receive) = std::sync::mpsc::sync_channel::<(&'static str, Option<i32>)>(1);
    let worker = std::thread::Builder::new().name("relax-exit".into()).spawn(move || {
        let Ok((why, code)) = receive.recv() else { return };
        EXIT_PERSIST.store(true, Ordering::SeqCst);
        exit_mark("start");
        remove_present_report();
        if let Some(code) = code { report("exit", &code.to_string()); }
        // background compilers stop and release the unit: the errors, the panic's report and
        // the summary below read it under the lock (summary_inner's quiesce re-enters it)
        let up = unsafe { RUN_UNIT };
        let got = !up.is_null() && jit::quiesce(exit_quiesce_ms());
        flush_errors(false);
        if let Some(p) = RUN_PANIC.get() {
            // the message itself was printed when main returned
            let rep = if got { unsafe { (&*up).report(p) } } else { "compiler busy; backtrace unavailable at exit".to_string() };
            eprintln!("relax-run: main {} report: {}", p.kind, rep);
            report("panic", &format!("main {}: {} -- report: {}", p.kind, p.message, rep));
        }
        if let Some(code) = code {
            crate::why::event("boundary", "run-exit", 0, "", Some(crate::why::Cause::new("", 0, "exit", &code.to_string())));
        }
        exit_mark("errors");
        summary_inner(why);
        if got { jit::unlock_unit(); }
        EXIT_PERSIST.store(false, Ordering::SeqCst);
        if let Some(dcx) = RUN_DIAGNOSTICS.lock().unwrap().as_ref() { dcx.flush_delayed(); }
        exit_mark("summary tail");
        exit_report();
        crate::tui::finish(false);
    });
    // Failure to start optional cleanup must not turn a successful run into a failure.
    if let Ok(worker) = worker { let _ = EXIT_SUMMARY.set(ExitSummary { request, worker, code: std::sync::OnceLock::new() }); }
}

fn finish_run(why: &'static str, code: Option<i32>) {
    crate::borrowck::lazy::stop();
    let Some(exit) = EXIT_SUMMARY.get() else { return };
    // Only the first caller requests cleanup. In particular the later atexit hook
    // does not spend a second budget after a JIT exit hook ran.
    static DONE: AtomicBool = AtomicBool::new(false);
    if DONE.swap(true, Ordering::AcqRel) { return; }
    EXIT_CALLER_HOLDS.store(jit::lock_depth() > 0, Ordering::SeqCst);
    if exit.request.try_send((why, code)).is_err() { return; }
    // 100 ms for the cleanup, counted from the end of the cache write; the write itself only
    // has a hang guard (a store on a stalled disk must not keep the process forever)
    let start = Instant::now();
    let mut deadline = start + std::time::Duration::from_millis(100);
    while !exit.worker.is_finished() {
        let now = Instant::now();
        if EXIT_PERSIST.load(Ordering::SeqCst) && now.duration_since(start).as_secs() < 30 {
            deadline = now + std::time::Duration::from_millis(100);
        }
        if now >= deadline { break; }
        std::thread::sleep(std::time::Duration::from_millis(1));
    }
}

/// RELAX_EXIT_TRACE=1: wall ms of each part of the exit work (at_exit), one line at the end.
fn exit_trace() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("RELAX_EXIT_TRACE").is_some())
}
static EXIT_MARKS: std::sync::Mutex<Vec<(&'static str, u64)>> = std::sync::Mutex::new(Vec::new());
/// Ends the exit-work part `name` (the time since the previous mark).
pub(crate) fn exit_mark(name: &'static str) {
    if exit_trace() {
        let mut marks = EXIT_MARKS.lock().unwrap_or_else(|e| e.into_inner());
        // a cache flush during the run also marks: the exit's parts start at its own start
        if name == "start" { marks.clear(); }
        marks.push((name, jit::wall_ns()));
    }
}
fn exit_report() {
    if !exit_trace() { return; }
    let marks = std::mem::take(&mut *EXIT_MARKS.lock().unwrap_or_else(|e| e.into_inner()));
    let Some(&(_, t0)) = marks.first() else { return };
    let mut prev = t0;
    let parts: Vec<String> = marks.iter().skip(1).map(|&(n, t)| { let d = t.saturating_sub(prev); prev = t; format!("{}={:.1}", n.replace(' ', "_"), d as f64 / 1e6) }).collect();
    eprintln!("relax-exit: total_ms={:.1} {} (thread {:?}, t={:.0} ms)", prev.saturating_sub(t0) as f64 / 1e6, parts.join(" "), std::thread::current().name().unwrap_or("?"), crate::clock::ms_since_start());
}


/// The collected-program store holds this run's program (restored whole from it, or recorded
/// by this run): neither the mid-run writes nor the exit encode it again. Encoding it took
/// 0.3-0.6 s of every exit (Calculator, Files) and rewrote the store whenever the run's type
/// interner had grown.
static COLLECTED_CURRENT: AtomicBool = AtomicBool::new(false);

/// Run-time crates must not become part of the next boot's collected image. The caller
/// holds both front-end and unit locks, before appending the first such crate. Publication
/// still belongs to the post-present writer; an already-restored/written boot needs no copy.
pub(crate) fn preserve_collected_boot(u: &mut jit::Unit) {
    if !COLLECTED_CURRENT.load(Ordering::Relaxed) && front_recordable() {
        if let Some(c) = u.cache.as_mut() { c.preserve_collected_boot(&u.prog, &u.tcx); }
    }
}
/// A mid-run write tried to record the collected program (once per run; the exit tries again
/// only if it is still not current).
static MID_COLLECTED_TRIED: AtomicBool = AtomicBool::new(false);
/// A mid-run write recorded the startup manifest (its window had closed).
static MID_MANIFEST_DONE: AtomicBool = AtomicBool::new(false);

/// Compile totals since boot, the startup list for `--ahead`, and the JSON report.
/// jit::wall_ns() when main was called (RELAX_MAIN_COMPILE_LOG's time base)
static MAIN_START_WALL: AtomicU64 = AtomicU64::new(0);

/// Front images, crate records and the collected graph describe the sources the run booted
/// from. A live session records them too, until its first edit: from then on the Program holds
/// reloaded file versions that are not the crate versions its stores are named after.
fn front_recordable() -> bool {
    crate::front::enabled() && crate::reload::edited_crates().is_empty()
}

/// The app was asked to quit (SIGTERM, SIGINT, SIGHUP: platform termination_signal.rs): the
/// cache is written now, on its own thread, while the app shuts down -- the startup manifest
/// (its window closes here), this run's code and front images, and the collected program.
/// A cold app's shutdown compiles for seconds before the exit write; a harness that kills it
/// 5 s after SIGTERM left no manifest and no collected program, so every relaunch was cold.
/// The exit write still runs and adds what came after.
pub(crate) extern "C" fn relax_quit_requested() {
    crate::tui::abnormal();
    static ONCE: AtomicBool = AtomicBool::new(false);
    jit::QUIT_SEEN.store(true, Ordering::Relaxed);
    if ONCE.swap(true, Ordering::SeqCst) || unsafe { RUN_UNIT }.is_null() { return; }
    if jit::FIRST_PRESENT.load(Ordering::Acquire) {
        jit::ORDER_UNTIL_NS.fetch_min(jit::wall_ns(), Ordering::Relaxed);
    }
    let _ = std::thread::Builder::new().name("relax-quit-write".to_string()).spawn(|| {
        let _mem = crate::memstat::tag(crate::memstat::Tag::CacheStore);
        let t = Instant::now();
        // the unit lock is busy while the app's shutdown compiles: retry for a bounded time
        let mut r = None;
        while t.elapsed().as_millis() < 4000 {
            r = mid_flush(true, true).or(r);
            if r.is_some() && (COLLECTED_CURRENT.load(Ordering::Relaxed) || MID_COLLECTED_TRIED.load(Ordering::Relaxed)) { break; }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
        verbose!("relax-cache: quit write at t={:.0} ms: {:?} (entries, front images), collected {} in {:.1} ms",
            crate::clock::ms_since_start(), r, COLLECTED_CURRENT.load(Ordering::Relaxed), t.elapsed().as_secs_f64() * 1e3);
    });
}

/// A write of the disk cache while the program runs (front images, code, borrowck verdicts):
/// programs that never reach Relax's exit summary (killed, or a framework ends the process
/// with _exit) keep what they compiled. The unit lock is held only to take things out of the
/// cache; images are encoded and stores written without it. Ok(None): the unit was busy.
/// The front images of the program's files the store does not have yet (front.rs), queued
/// for the next spill; the count.
/// `relax check`: this load's files written as front images and its crate records, as a run's
/// boot does (`push_front_images` + `record_front_crates` + the front graph), so the next check
/// maps them. Only when the cache is on and some file was parsed (nothing new otherwise).
fn record_check_front(u: &mut Unit, options: &crate::options::Options) {
    if !front_recordable() { return; }
    // the loader's front graph write runs on its own thread from load finish: a check ends
    // sooner than a run's first present, so it waits for that write here (else the process
    // exited under it, no graph certificate was ever recorded, and every check validated each
    // crate image again -- or re-parsed, when a selection could not be proven without it)
    if u.prog.front_restored.iter().all(|r| *r) {
        let r = crate::cache::Cache::flush_front_graphs();
        verbose!("relax-check: front graph {:?}", r.err());
        return;
    }
    let Some(mode) = crate::cache::mode_from_env(options) else { return };
    let t = Instant::now();
    let mut c = match crate::cache::Cache::open_collected(u, mode, None) {
        Ok(c) => c,
        Err(e) => { verbose!("relax-check: front images not written: {}", e); return; }
    };
    let n = push_front_images(&u.prog, &mut c);
    c.record_front_crates(&u.prog);
    let written = match c.spill_take() {
        Some(s) if crate::cache::ColdFront::enabled(options) => s.write_mapped().map(|_| ()),
        Some(s) => s.write().map(|_| ()),
        None => Ok(()),
    };
    let graph = crate::cache::Cache::flush_front_graphs();
    verbose!("relax-check: {} front images written ({:?}, graph {:?}) in {:.0} ms", n, written.err(), graph.err(), t.elapsed().as_secs_f64() * 1e3);
}

fn push_front_images(prog: &crate::program::Program, c: &mut crate::cache::Cache) -> usize {
    let mut n = 0;
    for i in 0..prog.files.len() {
        let f = &prog.files[i];
        let (Some(path), Some(&krate)) = (prog.file_paths.get(i), prog.file_crate.get(i)) else { continue };
        let want_part = f.lazy.is_some() && crate::front::has_part_image(f) && !f.part.get().map_or(false, |p| p.toks.is_mapped());
        let source_hash = f.source_hash(path);
        let (m, p) = c.reserve_front(krate, path, source_hash, !f.src.is_mapped(), want_part);
        if m { c.push_front(krate, path, source_hash, false, f.clone()); }
        if p { c.push_front(krate, path, source_hash, true, f.clone()); }
        n += m as usize + p as usize;
    }
    n
}

/// `wait`: the warm record's writes (after first present, at a quit) wait for the unit lock,
/// which a cold run's compiles hold nearly all the time (lock_unit announces the waiter, so
/// background compilers yield between steps); other writes skip a busy unit.
fn mid_flush(quiet: bool, wait: bool) -> Option<(usize, usize)> {
    // the first write comes after the start: the mapped front images are checksummed now
    crate::cache::verify_front_images();
    let up = unsafe { RUN_UNIT };
    // one unit call: waits for the unit when `wait`, else only if it is free now
    fn unit_call<R>(wait: bool, f: impl FnOnce() -> R) -> Option<R> {
        if wait { Some(crate::owner::call(crate::owner::Class::App, f)) } else { crate::owner::call_within(crate::owner::Class::Background, 0, f) }
    }
    if up.is_null() {
        return None;
    }
    let mut parts = [0f64; 3];
    let session = unsafe { (*std::ptr::addr_of!((*up).prog.session)).clone() };
    let options = &session.options;
    let mut n_imgs = 0;
    // the files whose front images this write holds: the collected program below is recorded
    // only if no file was loaded since (its restore maps every file from these images)
    let mut imaged_files = usize::MAX;
    let Some(Some((held, spill))) = unit_call(wait, || {
    let held = Instant::now();
    let spill = {
        let u = unsafe { &mut *up };
        // the startup manifest, once its window has closed (first present + 5 s after main):
        // what the exit recorded before, so a killed or force-quit app starts warm too; the exit
        // writes it again only if O2 code replaced startup code since (record_manifest)
        if u.cache.is_some() && jit::FIRST_PRESENT.load(Ordering::Acquire) && jit::wall_ns() >= jit::ORDER_UNTIL_NS.load(Ordering::Relaxed) && !MID_MANIFEST_DONE.swap(true, Ordering::Relaxed) {
            let order = u.start_order.clone();
            let mut cache = u.cache.take();
            if let Some(c) = cache.as_mut() {
                // a frame's lazy compile goes first: the manifest is made again by a later write
                let stop = || jit::main_waiting() && !jit::QUIT_SEEN.load(Ordering::Relaxed);
                if !c.record_manifest(u, crate::layout::root_crate(), &order, jit::ORDER_PRESENT_LEN.load(Ordering::Relaxed), &stop) {
                    MID_MANIFEST_DONE.store(false, Ordering::Relaxed);
                    verbose!("relax-cache: startup manifest yielded to the main thread; retried later");
                }
            }
            u.cache = cache;
        }
        parts[0] = held.elapsed().as_secs_f64() * 1e3;
        let Some(c) = u.cache.as_mut() else {
            return None;
        };
        for (k, v) in crate::borrowck::lazy::take_verdict_keys() {
            c.record_borrowck(k, v);
        }
        if front_recordable() {
            n_imgs += push_front_images(&u.prog, c);
            parts[1] = held.elapsed().as_secs_f64() * 1e3;
            c.record_front_crates(&u.prog);
            parts[2] = held.elapsed().as_secs_f64() * 1e3;
            imaged_files = u.prog.files.len();
        }
        c.spill_take()
    };
    Some((held, spill))
    }) else { return None };
    let held1 = held.elapsed().as_secs_f64() * 1e3;
    let (n, mut stores) = match spill {
        Some(s) if crate::cache::ColdFront::enabled(options) => s.write_mapped().ok()?,
        Some(s) => (s.write().ok()?, Vec::new()),
        None => (0, Vec::new()),
    };
    let graph_ready = jit::FIRST_PRESENT.load(Ordering::Acquire)
        && crate::cache::Cache::flush_front_graphs().is_ok();
    // the collected program, once per run and only when the program is quiet (it is encoded
    // under the unit and front-end locks): not at the exit
    if graph_ready && quiet && !COLLECTED_CURRENT.load(Ordering::Relaxed) && !MID_COLLECTED_TRIED.load(Ordering::Relaxed) {
        // not when a file was loaded since this write took its front images (its restore maps
        // every file from them); a later quiet flush or the exit tries again. Files the lazy
        // selection still skips travel in the image (skipped_files, deferred imports).
        // Encoded under the locks, but never in the main thread's way: the encode stops when
        // the main thread waits for the unit lock (a frame's lazy compile) and a later pass
        // tries again; the store write runs after the locks are released.
        if let Some((ready, retired_boot, t)) = unit_call(wait, || {
            let mut ready = None;
            let mut retired_boot = None;
            let t = Instant::now();
            if let Some(_front) = jit::front_write_within(if jit::QUIT_SEEN.load(Ordering::Relaxed) { 1000 } else { 50 }) {
                let u = unsafe { &mut *up };
                // files the post-boot loader loaded since this write took its front images (a
                // run that did not restore loads for seconds after present): their images are
                // written now, under the locks, so the record can be made in this pass
                if wait && u.prog.files.len() != imaged_files && front_recordable() {
                    if let Some(c) = u.cache.as_mut() {
                        push_front_images(&u.prog, c);
                        c.record_front_crates(&u.prog);
                        let written = match c.spill_take() {
                            Some(s) if crate::cache::ColdFront::enabled(options) => s.write_mapped().map(|(_, more)| stores.extend(more)).is_ok(),
                            Some(s) => s.write().is_ok(),
                            None => true,
                        };
                        if written { imaged_files = u.prog.files.len(); }
                    }
                }
                if let Some(c) = u.cache.as_mut().filter(|_| u.prog.files.len() == imaged_files) {
                    let stop = || jit::main_waiting() && !jit::QUIT_SEEN.load(Ordering::Relaxed);
                    match c.encode_collected(&u.prog, &u.tcx, &stop) {
                        crate::cache::CollectedRecord::Ready(dest, payload) => { MID_COLLECTED_TRIED.store(true, Ordering::Relaxed); ready = Some((u.prog.session.options.verbose.then_some(c.collected_crates(&u.prog)), dest, payload)); }
                        crate::cache::CollectedRecord::Current => { MID_COLLECTED_TRIED.store(true, Ordering::Relaxed); COLLECTED_CURRENT.store(true, Ordering::Relaxed); retired_boot = Some(c.finish_collected()); }
                        crate::cache::CollectedRecord::Yielded => verbose!("relax-collected: record yielded to the main thread after {:.1} ms; retried later", t.elapsed().as_secs_f64() * 1e3),
                        crate::cache::CollectedRecord::Failed => MID_COLLECTED_TRIED.store(true, Ordering::Relaxed),
                    }
                }
            }
            (ready, retired_boot, t)
        }) {
            if std::env::var_os("RELAX_CACHE_TRACE").is_some() { verbose!("relax-cache: collected record held the unit lock {:.1} ms", t.elapsed().as_secs_f64() * 1e3); }
            drop(retired_boot);
            if let Some((report, dest, payload)) = ready {
                if crate::cache::Cache::commit_collected(report, dest, payload).is_some() {
                    COLLECTED_CURRENT.store(true, Ordering::Relaxed);
                    let retired_boot = crate::owner::call(crate::owner::Class::App, || unsafe { &mut *up }.cache.as_mut().map(|c| c.finish_collected()));
                    drop(retired_boot);
                }
            }
        }
    }
    if std::env::var_os("RELAX_CACHE_TRACE").is_some() { verbose!("relax-cache: mid write held the unit lock {:.1} ms (manifest to {:.1}, front images to {:.1}, crate records to {:.1}, then spill)", held1, parts[0], parts[1], parts[2]); }
    if crate::cache::ColdFront::enabled(options) {
        // Files map their front images in chunks of 128, each under the locks for a few ms,
        // with the main thread let in between (all 1100 of a cold Calculator at once held
        // them 65-170 ms right after the first present: a frame's lazy compile waited).
        let (mut installed, mut next, mut tries, mut max_held) = (false, 0usize, 0, 0f64);
        loop {
            let (done, held) = crate::owner::call(crate::owner::Class::App, || {
            let held = Instant::now();
                let front_guard = jit::front_write();
                let u = unsafe { &mut *up };
                let mut done = false;
                if let Some(c) = u.cache.as_mut() {
                    if !installed { c.install_front_stores(std::mem::take(&mut stores)); installed = true; }
                    // Lowering is excluded by the unit lock; ahead type checking and borrowck
                    // use FRONT_RW (raw Program pointers, not file Arcs), so exclude them too.
                    // Other users owning another Arc keep their heap arrays. The encoder's
                    // Arcs were dropped by the writer before attempting exclusive access here.
                    let prog = &mut u.prog;
                    let end = (next + 128).min(prog.files.len());
                    crate::program::without_std_shares(&mut prog.files, &prog.file_paths, |files| {
                        for i in next..end.min(files.len()) {
                            let file = &mut files[i];
                            let Some(path) = prog.file_paths.get(i) else { continue };
                            let source_hash = file.source_hash(path);
                            let main = (!file.src.is_mapped()).then(|| c.front_image(path, source_hash)).flatten();
                            let part = file.part.get().filter(|p| !p.toks.is_mapped()).and_then(|_| c.front_part_image(path, source_hash));
                            if main.is_none() && part.is_none() { continue; }
                            let Some(pf) = std::sync::Arc::get_mut(file) else {
                                crate::front::SHARED.fetch_add(1, Ordering::Relaxed);
                                continue;
                            };
                            if let Some(img) = main { crate::front::apply(path, pf, img); }
                            if let (Some(img), Some(&k)) = (part, prog.file_crate.get(i)) {
                                crate::front::swap_part(path, pf, img, &prog.crates[k as usize].cfg);
                            }
                        }
                    });
                    next = end;
                    done = next >= prog.files.len();
                } else if installed {
                    done = true;
                }
                drop(front_guard);
            (done, held)
            });
            max_held = max_held.max(held.elapsed().as_secs_f64() * 1e3);
            if done { break; }
            if !installed {
                // the exit has the cache: retry a little later, a bounded number of times
                tries += 1;
                if tries >= 50 { break; }
                std::thread::sleep(std::time::Duration::from_millis(20));
                continue;
            }
            let t = Instant::now();
            while jit::main_waiting() && t.elapsed().as_millis() < 50 { std::thread::yield_now(); }
        }
        if std::env::var_os("RELAX_CACHE_TRACE").is_some() { verbose!("relax-cache: front image install held the unit lock {:.1} ms at most", max_held); }
    }
    // All temporary encoders and retired boot arrays are now outside compiler locks.
    crate::memstat::trim();
    Some((n, n_imgs))
}

pub(crate) fn summary(why: &'static str) {
    if why == "stats" { summary_inner(why); }
    else { finish_run(why, None); }
}

fn summary_inner(why: &str) {
    crate::fncost::mark("summary");
    // Independent of the Unit lock: still emit when exit quiescence times out.
    if why != "stats" { crate::exec_profile::report(false); }
    if why != "stats" {
        // the run is ending: background borrow checks stop at their next preemption point
        // (nothing waits for them; finished verdicts are stored below)
        crate::borrowck::lazy::stop();
        crate::warm::finish();
        if let Some(console) = GANDALF_CONSOLE.lock().unwrap_or_else(|e| e.into_inner()).take() { console.detach(); }
        exit_mark("warm+console");
    }
    if why != "stats" && std::env::var_os("RELAX_CACHE_FP").is_some() {
        let late = crate::sip::late_inputs();
        for (c, k, n, h) in &late {
            verbose!("relax-cache: late {} {} {} {:032x}", c, if *k == crate::sip::LATE_FILE { "file" } else { "env" }, n, h);
        }
        verbose!("relax-cache: {} late inputs", late.len());
    }
    let up = unsafe { RUN_UNIT };
    if up.is_null() {
        return;
    }
    let session = unsafe { (*std::ptr::addr_of!((*up).prog.session)).clone() };
    let options = &session.options;
    // at the end of the run the background compilers stop and release the unit (a mid-run
    // "stats" summary keeps them going); the summary reads it under the lock
    let holder = jit::lock_holder();
    let t_wait = std::time::Instant::now();
    // the end of the run never waits on compiles: other threads' builds are abandoned at their next
    // safe point (jit::quiesce); a holder still busy after EXIT_QUIESCE_MS costs this run's
    // summary + cache pack
    let preamble = |got: bool| -> bool {
        if got && holder != "nobody" && t_wait.elapsed().as_micros() > 100 && !SILENT.load(Ordering::Relaxed) {
            verbose!("relax-run: {}: waited {:.1} ms for the unit lock (held by `{}`)", why, t_wait.elapsed().as_secs_f64() * 1e3, holder);
        }
        if why != "stats" { exit_mark("quiesce"); jit::tier1_stats_report(); }
        if !got {
            verbose!("relax-run: {}: no summary -- the unit lock is still held by thread `{}`", why, jit::lock_holder());
            return false;
        }
        true
    };
    let rest = || {
        if why != "stats" {
            let (ms, site) = jit::main_post_present_wait();
            verbose!("relax-run: main thread's longest unit-lock wait after first present: {:.1} ms (holder locked at {})", ms, site);
        }
        verbose!("relax-run: startup seeds skipped: {} initializers (demand evaluation required), {} recursive builds", jit::SEED_INITIALIZERS_SKIPPED.load(Ordering::Relaxed), jit::SEED_RECURSIVE_SKIPPED.load(Ordering::Relaxed));
        // borrowck lane: the background checker's summary, with or without the disk cache; checker
        // panics are counted and named, never silent
        if why != "stats" {
            crate::borrowck::lazy::print_summary(options);
        }
        if let Some(line) = crate::reload::session_summary() {
            verbose!("{}", line);
        }
        if why != "stats" { exit_mark("reports"); }
        // the disk cache: this run's new entries become a pack (unit lock held: no compiles)
        if why != "stats" {
            let u = unsafe { &mut *up };
            let order = std::mem::take(&mut u.start_order);
            let mut cache = u.cache.take();
            if let Some(c) = cache.as_mut() {
                c.record_manifest(u, crate::layout::root_crate(), &order, jit::ORDER_PRESENT_LEN.load(Ordering::Relaxed), &|| false);
            }
            u.cache = cache;
            exit_mark("manifest");
            if let Some(c) = u.cache.as_mut() {
                // borrowck lane: clean verdicts found in the background are remembered
                for (k, v) in crate::borrowck::lazy::take_verdict_keys() {
                    c.record_borrowck(k, v);
                }

                // front images of the files the store does not have yet (front.rs) and the crate
                // records: a run quit before its first mid-run write has all of them left
                if front_recordable() {
                    for i in 0..u.prog.files.len() {
                        let f = &u.prog.files[i];
                        let (Some(path), Some(&krate)) = (u.prog.file_paths.get(i), u.prog.file_crate.get(i)) else { continue };
                        let want_part = f.lazy.is_some() && crate::front::has_part_image(f) && !f.part.get().map_or(false, |p| p.toks.is_mapped());
                        let source_hash = f.source_hash(path);
                        let (m, p) = c.reserve_front(krate, path, source_hash, !f.src.is_mapped(), want_part);
                        if m { c.push_front(krate, path, source_hash, false, f.clone()); }
                        if p { c.push_front(krate, path, source_hash, true, f.clone()); }
                    }
                    c.record_front_crates(&u.prog);
                }
                exit_mark("front images");
                let t = std::time::Instant::now();
                // The graph writer opens the crate records just queued above.
                // Flush them first, as the mid-run writer does, then publish the
                // demand parts/graph and finally its collected image. Trying the
                // graph first can fail on a missing crate store and skip the very
                // flush that would make it recordable (also on boot-only exits).
                let r = c.flush().and_then(|written| {
                    crate::cache::Cache::flush_front_graphs()?;
                    Ok(written)
                });
                exit_mark("flush");
                // the collected program, unless restored whole or written mid-run; never waits long
                // for a reader: an app thread parked for good (EXITING) may hold one
                if r.is_ok() && front_recordable() && !COLLECTED_CURRENT.load(Ordering::Relaxed) {
                    if let Some(_front) = jit::front_write_within(2000) {
                        exit_mark("front lock");
                        if c.record_collected(&u.prog, &u.tcx).is_some() { COLLECTED_CURRENT.store(true, Ordering::Relaxed); }
                        exit_mark("collected");
                    } else {
                        verbose!("relax-collected: not recorded at exit: the front end is still read by another thread");
                    }
                }
                if !options.verbose {
                    if let Err(e) = &r { eprintln!("relax-cache: write: {}", e); }
                }
                let st = &c.stats;
                verbose!(
                    "relax-cache: {} hits, {} misses, {} link failures, {} refused by their dependency certificate (per-item cpu: body digests {:.1} ms, certificates written {:.1} ms, checked {:.1} ms) (link {:.1} ms wall with the lock; by speculative workers {} hits {:.1} ms), {} recorded, {} not storable {:?}; written {:?} in {:.1} ms",
                    st.hits, st.misses, st.link_fail, st.cert_rejects, st.body_ns as f64 / 1e6, st.cert_write_ns as f64 / 1e6, st.cert_check_ns as f64 / 1e6, st.link_ns as f64 / 1e6, st.spec_hits, st.spec_link_ns as f64 / 1e6, st.recorded, st.unencodable, c.why_unencodable, r, t.elapsed().as_secs_f64() * 1e3
                );
                if let Some(s) = crate::front::summary() {
                    verbose!("{}", s);
                }
                if c.mode == crate::cache::Mode::Verify {
                    let st = &c.stats;
                    verbose!("relax-cache: verify: {} same, {} DIFFERENT", st.verify_same, st.verify_diff);
                }
            }
        }
        if why != "stats" {
            crate::mainprof::write(unsafe { &*up });
            crate::cache::write_trace();
            exit_mark("profiles");
        }
        let u = unsafe { &*up };
        if crate::memstat::enabled() {
            crate::memstat::print(why, &crate::memreport::unit_sizes(u));
            let lp = |i: usize| crate::parser::LAZY_PARSED[i].load(Ordering::Relaxed);
            eprintln!("relax-mem: lazy fn bodies: {} files parsed their skipped bodies ({} bodies)", lp(0), lp(1));
            let w = crate::parser::LAZY_WHY_PARSED.lock().unwrap();
            if !w.is_empty() {
                eprintln!("relax-mem: lazy parts parsed by: {}", w.iter().map(|(k, v)| format!("{} {}", k, v)).collect::<Vec<_>>().join(", "));
            }
            if let Some(set) = crate::typeck::CHECKED_DEFS.lock().unwrap().as_ref() {
                // a lazy parse by item parses the checked defs' bodies; by file, every body of the files they are in
                let mut files = std::collections::HashSet::new();
                let mut item_exprs = 0usize;
                for &d in set {
                    let df = u.prog.def(crate::program::DefId(d));
                    files.insert(df.file);
                    let it = u.prog.files[df.file as usize].ast.item(df.item);
                    item_exprs += (it.ranges[1] - it.ranges[0]) as usize;
                }
                let all: usize = u.prog.files.iter().map(|f| f.ast.exprs.len()).sum();
                let touched: usize = files.iter().map(|f| u.prog.files[*f as usize].ast.exprs.len()).sum();
                eprintln!("relax-mem: lazy-body need: {} defs checked ({} exprs of {} = {:.0}%); {} of {} files touched ({:.0}% of exprs)", set.len(), item_exprs, all, 100.0 * item_exprs as f64 / all as f64, files.len(), u.prog.files.len(), 100.0 * touched as f64 / all as f64);
            }
        }
        let s = &u.stats;
        let now = crate::clock::ms_since_start();
        if !SILENT.load(Ordering::Relaxed) {
        verbose!(
            "relax-run: {} at t={:.0} ms (main from t={} ms): compiled {} fns, {} KB code, {} compile errors; cpu typeck {:.0} ms, lower {:.0} ms, opt {:.0} ms, codegen {:.0} ms",
            why,
            now,
            MAIN_START_MS.load(Ordering::Relaxed),
            s.compiled,
            s.code_bytes / 1024,
            u.errors.len(),
            s.typeck_ns as f64 / 1e6,
            s.lower_ns as f64 / 1e6,
            s.opt_ns as f64 / 1e6,
            s.codegen_ns as f64 / 1e6
        );
        }
        crate::tui::print_slowest();
        // wall clocks are jit::wall_ns() (started at the first call of it, at boot)
        verbose!(
            "relax-run: compile wall {:.0} ms (lock held); last compile ended at {:.0} ms after the clock start",
            s.compile_wall_ns as f64 / 1e6,
            s.last_compile_end_ns as f64 / 1e6
        );
        let rt = jit::RT_LAZY.load(Ordering::Relaxed);
        if rt > 0 {
            verbose!("relax-run: real-time threads compiled {} fns lazily, stalled {:.1} ms in all", rt, jit::RT_LAZY_NS.load(Ordering::Relaxed) as f64 / 1e6);
        }
        {
            let n: Vec<f64> = jit::SPLIT_NS.iter().map(|x| x.load(Ordering::Relaxed) as f64 / 1e6).collect();
            let (mut built, mut used) = (0, 0);
            for f in u.fns.iter() {
                if f.spec_state > 0 {
                    built += 1;
                }
                if f.spec_state == 2 {
                    used += 1;
                }
            }
            if built > 0 || n[0] > 0.0 {
                verbose!(
                    "relax-run: pipelined compile: callers front {:.0} ms locked, back {:.0} ms unlocked, relock wait {:.0} ms, in-flight waits {:.0} ms; speculative {} built ({} called, {} unused; {} expired after RELAX_SPEC_TTL_MS, {:.0} MB freed), workers front {:.0} ms back {:.0} ms, {} yields, {} cold calls skipped, {} priority relocks{}",
                    n[0], n[1], n[2], n[3], built, used, built - used, jit::SPEC_EXPIRED[0].load(Ordering::Relaxed), jit::SPEC_EXPIRED[1].load(Ordering::Relaxed) as f64 / 1048576.0, n[4], n[5], jit::SPEC_YIELDS.load(Ordering::Relaxed), jit::SPEC_COLD_SKIPPED.load(Ordering::Relaxed), jit::SPEC_PRIORITY.load(Ordering::Relaxed), if jit::spec_hot_only(options) { " (fall-through only)" } else { "" }
                );
            }
        }
        if !SILENT.load(Ordering::Relaxed) {
            let h = |i: usize| jit::LOCK_HELD_NS[i].load(Ordering::Relaxed) as f64 / 1e6;
            verbose!("relax-run: unit lock held: main {:.0} ms, workers {:.0} ms, other threads {:.0} ms (t={:.0} ms)", h(0), h(1), h(2), crate::clock::ms_since_start());
        }
        let ah = |i: usize| jit::AHEAD_STATS[i].load(Ordering::Relaxed);
        if ah(0) + ah(2) > 0 && !SILENT.load(Ordering::Relaxed) {
            verbose!("relax-run: type checks ahead (off the lock): {} bodies ({} taken by builds, {} with errors), cpu callers {:.0} ms, workers {:.0} ms", ah(0), ah(1), ah(2), ah(3) as f64 / 1e6, ah(4) as f64 / 1e6);
        }
        if s.ctfe_data + s.ctfe_code > 0 && !SILENT.load(Ordering::Relaxed) {
            verbose!("relax-run: constant initializers: {} evaluated to data, {} compiled and run; evaluation cpu {:.1} ms", s.ctfe_data, s.ctfe_code, s.ctfe_ns as f64 / 1e6);
        }
        // RELAX_MAIN_COMPILE_LOG=<path>: the main thread's compiles, ms since main started: app
        // execution vs compile on the critical path. Per line: start end slot how typeck_ahead
        // lock_wait front back relock inflight_wait (ms) slot-key name (spaces as `~`), then `cpu` front opt codegen (thread cpu ms) `insts` entering opt / codegen; `slot` indexes RELAX_COMPILE_REPORT's rows
        if let Ok(path) = std::env::var("RELAX_MAIN_COMPILE_LOG") {
            let base = MAIN_START_WALL.load(Ordering::Relaxed);
            let mut out = format!("# package {}\n", ROOT_DIR.lock().unwrap());
            let ms = |ns: u64| ns as f64 / 1e6;
            for r in jit::MAIN_COMPILES.lock().unwrap().iter() {
                let how = jit::MAIN_HOW_NAMES.get(r.how as usize).copied().unwrap_or("?");
                let (name, hint) = if (r.slot as usize) < u.fns.len() {
                    let f = &u.fns[r.slot as usize];
                    let hint = jit::slot_key(u, r.slot);
                    (f.name.as_str(), hint)
                } else {
                    ("-", "-".to_string())
                };
                out.push_str(&format!(
                    "{:.3} {:.3} {} {} {:.3} {:.3} {:.3} {:.3} {:.3} {:.3} {} {}  cpu {:.3} {:.3} {:.3} insts {} {}\n",
                    ms(r.start.saturating_sub(base)), ms(r.end.saturating_sub(base)), r.slot, how, ms(r.ns[0]), ms(r.ns[1]), ms(r.ns[2]), ms(r.ns[3]), ms(r.ns[4]), ms(r.ns[5]), hint.replace(' ', "~"), name.replace(' ', "~"), ms(r.cpu[0]), ms(r.cpu[1]), ms(r.cpu[2]), r.insts[0], r.insts[1]
                ));
            }
            let _ = std::fs::write(path, out);
        }
        let q = jit::TIER_QUEUED.load(Ordering::Relaxed);
        if q > 0 {
            verbose!(
                "relax-run: O3: {} hot, {} installed ({} rebuild requests), {} dropped {:?}; {} RIRs rebuilt ({:.0} ms); cpu {:.0} ms with the lock, {:.0} ms without{}",
                q,
                s.tier1_installed,
                s.tier1_retier,
                s.tier1_dropped,
                s.tier1_drop_why,
                jit::TIER1_RIR_REBUILT[0].load(Ordering::Relaxed),
                jit::TIER1_RIR_REBUILT[1].load(Ordering::Relaxed) as f64 / 1e6,
                s.tier1_locked_ns as f64 / 1e6,
                s.tier1_free_ns as f64 / 1e6,
                {
                    let n = jit::NESTED_AT_YIELD.load(Ordering::Relaxed);
                    if n == 0 { String::new() } else { format!("; UNBALANCED unit lock: {} nested at a yield, {} left held by a O3 job", n & 0xffff_ffff, n >> 32) }
                }
            );
        }
        let mut tl = String::new();
        for (i, (n, w)) in s.timeline.iter().enumerate() {
            if *n > 0 {
                tl.push_str(&format!(" {}s:{}fns/{}ms", i as f64 / 10.0, n, w / 1_000_000));
            }
        }
    if !SILENT.load(Ordering::Relaxed) {     verbose!("relax-run: compile timeline (100 ms buckets):{}", tl); }
        if std::env::var("RELAX_PASS_TIMES").is_ok() {
            let mut passes = String::new();
            for i in 0..crate::opt::PASS_NAMES.len() {
                passes.push_str(&format!("{} {:.0}  ", crate::opt::PASS_NAMES[i], crate::opt::PASS_NS[i].load(Ordering::Relaxed) as f64 / 1e6));
            }
    if !SILENT.load(Ordering::Relaxed) {         verbose!("relax-run: opt passes (cpu ms): {}", passes); }
            verbose!("relax-run: invokes {} seen, {} made plain calls", crate::opt::INVOKES_SEEN.load(Ordering::Relaxed), crate::opt::INVOKES_DEMOTED.load(Ordering::Relaxed));
        }
        if crate::rir::unwind_stats_on() {
            let st = &crate::rir::UNWIND_STATS;
            verbose!("relax-run: unwind bytes: pads {} KB, landing stubs {} KB, trailers {} KB; invokes emitted {}", st[0].load(Ordering::Relaxed) / 1024, st[1].load(Ordering::Relaxed) / 1024, st[2].load(Ordering::Relaxed) / 1024, st[3].load(Ordering::Relaxed));
        }
        // startup list: non-generic fns compiled during this run, in slot order (first-call order)
        let mut list = String::new();
        for f in u.fns.iter() {
            if let FnKey::Inst(d, args) = &f.key {
                if f.compiled && args.is_empty() {
                    list.push_str(&u.prog.def_path(*d));
                    list.push('\n');
                }
            }
        }
        let path = STARTUP_PATH.lock().unwrap().clone();
        if !path.is_empty() {
            if let Some(dir) = std::path::Path::new(&path).parent() {
                let _ = std::fs::create_dir_all(dir);
            }
            let _ = std::fs::write(&path, list);
        }
        // per-slot compile report: kind, crate, generic, compiled (= entered: compiles happen on
        // the first call through the lazy stub), RIR built, times inlined, cpu ns; last column
        // `spec`: 0 not built ahead, 1 built ahead and never called (wasted), 2 built ahead and
        // installed by its first call; `spec_depth`: speculation depth it was queued at (-1 none)
        if let Ok(p) = std::env::var("RELAX_COMPILE_REPORT") {
            let mut out = format!("# build: {}\n", crate::jit::PROVENANCE);
            out.push_str("kind\tcrate\tgeneric\tcompiled\trir\tinlined_into\tbuild_ns\tcg_ns\tsrc\tname\tspec\tspec_depth\torigin\ttrait\tself\thint\tcode_bytes\tO3\tframe0\tframe1\tslots0\tslots1\n");
            let frames = jit::FRAMES.lock().unwrap_or_else(|e| e.into_inner()).clone();
            let fslots = jit::FRAME_SLOTS.lock().unwrap_or_else(|e| e.into_inner()).clone();
            for (idx, f) in u.fns.iter().enumerate() {
                let (kind, krate, generic) = match &f.key {
                    FnKey::Inst(d, args) => ("inst", u.prog.syms.str(u.prog.crates[u.prog.def(*d).krate as usize].name).to_string(), !args.is_empty()),
                    FnKey::Closure(..) => ("closure", "-".to_string(), false),
                    FnKey::Shim(_) => ("shim", "-".to_string(), true),
                    FnKey::Glue(g, _) => (if *g == jit::GLUE_DROP { "drop" } else { "glue" }, "-".to_string(), true),
                    FnKey::Sandbox(_) => ("sandbox", "-".to_string(), false),
                };
                let src = jit::src_size(u, idx as u32);
                let (origin, tr, selfty) = report_origin(u, &f.key);
                // def path of a non-generic fn instance (jit::slot_key has every slot's full key)
                let hint = match &f.key {
                    FnKey::Inst(d, args) if args.is_empty() => crate::program::hint_path(&u.prog.defs, &u.prog.syms, &u.prog.files, *d),
                    _ => "-".to_string(),
                };
                out.push_str(&format!("{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n", kind, krate, generic as u8, f.compiled as u8, (f.rir.is_some() || f.build_ns > 0) as u8, f.inlined_into.len(), f.build_ns, f.cg_ns, src as i64, f.name, f.spec_state, if f.spec_depth == u8::MAX { -1 } else { f.spec_depth as i32 }, origin, tr, selfty, hint, if f.compiled { f.code_len } else { 0 }, !f.retired.is_empty() as u8, frames.get(idx).map_or(0, |x| x.0), frames.get(idx).map_or(0, |x| x.1), fslots.get(idx).map_or(0, |x| x.0), fslots.get(idx).map_or(0, |x| x.1)));
            }
            let _ = std::fs::write(&p, out);
            // code-size sanity: the largest O3 functions (an inliner gone wild shows here first;
            // R13's parser function was 1.9 MB)
            let mut t1: Vec<(u32, &str)> = u.fns.iter().filter(|f| f.compiled && !f.retired.is_empty()).map(|f| (f.code_len, f.name.as_str())).collect();
            t1.sort_unstable_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(b.1)));
            let top: Vec<String> = t1.iter().take(5).map(|(n, name)| format!("{} {} KB", name, n / 1024)).collect();
            verbose!("relax-run: largest O3 functions: {}", if top.is_empty() { "none".to_string() } else { top.join(", ") });
            // stack sanity: the largest frames (O1 and O3)
            let mut fr: Vec<(u32, &str, &str)> = Vec::new();
            for (idx, f) in u.fns.iter().enumerate() {
                if let Some(&(a, b)) = frames.get(idx) {
                    if a > 0 {
                        fr.push((a, "t0", f.name.as_str()));
                    }
                    if b > 0 {
                        fr.push((b, "t1", f.name.as_str()));
                    }
                }
            }
            fr.sort_unstable_by(|a, b| b.0.cmp(&a.0).then(a.2.cmp(b.2)));
            let top: Vec<String> = fr.iter().take(8).map(|(n, t, name)| format!("{} ({}) {} KB", name, t, n / 1024)).collect();
            verbose!("relax-run: largest frames: {}", top.join(", "));
        }
        let rp = REPORT_PATH.lock().unwrap().clone();
        if !rp.is_empty() {
            let mut j = String::from("{\"phases\":{");
            for (i, (n, ms)) in PHASES.lock().unwrap().iter().enumerate() {
                if i > 0 {
                    j.push(',');
                }
                j.push_str(&format!("\"{}\":{:.1}", n.replace('"', ""), ms));
            }
            j.push_str(&format!(
                "}},\"main_ms\":{},\"end_ms\":{:.0},\"end\":\"{}\",\"compiled\":{},\"compile_errors\":{},\"typeck_ms\":{:.1},\"lower_ms\":{:.1},\"opt_ms\":{:.1},\"codegen_ms\":{:.1}}}\n",
                MAIN_START_MS.load(Ordering::Relaxed),
                now,
                why,
                s.compiled,
                u.errors.len(),
                s.typeck_ns as f64 / 1e6,
                s.lower_ns as f64 / 1e6,
                s.opt_ns as f64 / 1e6,
                s.codegen_ns as f64 / 1e6
            ));
            let _ = std::fs::write(&rp, j);
        }
    };
    if why == "stats" {
        if crate::owner::call_within(crate::owner::Class::App, 0, || { if preamble(true) { rest(); } }).is_none() {
            preamble(false);
        }
    } else if jit::quiesce(exit_quiesce_ms()) {
        // quiesce returns holding the unit lock; the summary is one unit call within that hold
        crate::owner::call(crate::owner::Class::App, || { if preamble(true) { rest(); } });
        jit::unlock_unit();
    } else {
        preamble(false);
    }
}

/// Compile report columns `origin`, `trait`, `self` of a slot: where its body's source is
/// (`s` the file itself, `r` a macro_rules expansion, `x` a proc-macro / built-in expansion such
/// as a derive), the trait of its impl (or the trait whose default method it instantiates) and
/// its first type argument (the Self of a default method instance).
fn report_origin(u: &jit::Unit, key: &FnKey) -> (&'static str, String, String) {
    let pos_origin = |file: u32, lo: u32| -> &'static str {
        let pf = &u.prog.files[file as usize];
        if lo < pf.src_len {
            "s"
        } else if pf.rules_exp.iter().any(|r| lo >= r.0 && lo <= r.1) {
            "r"
        } else {
            "x"
        }
    };
    match key {
        FnKey::Inst(d, args) => {
            let def = u.prog.def(*d);
            if !matches!(def.kind, DefKind::Fn | DefKind::AssocFn) {
                return ("-", String::new(), String::new());
            }
            let it = u.prog.files[def.file as usize].ast.item(def.item);
            let origin = pos_origin(def.file, it.lo);
            let mut tr = String::new();
            if def.parent != crate::program::NO_DEF {
                let p = u.prog.def(def.parent);
                match p.kind {
                    DefKind::Trait => tr = format!("T:{}", u.prog.syms.str(p.name)),
                    DefKind::Impl => {
                        tr = "I:".to_string();
                        let pf = &u.prog.files[p.file as usize];
                        if let crate::ast::ItemKind::Impl { trait_: Some(path), .. } = &pf.ast.item(p.item).kind {
                            if let Some(seg) = pf.ast.segs(path.segs).last() {
                                tr.push_str(pf.text(seg.name));
                            }
                        }
                    }
                    _ => {}
                }
            }
            let selfty = args.first().map(|t| crate::typeck::type_name(&u.prog, &u.tcx, *t)).unwrap_or_default();
            (origin, tr, selfty)
        }
        FnKey::Closure(file, ce, parent) => {
            let e = u.prog.files[*file as usize].ast.expr(crate::ast::ExprId(*ce));
            let origin = pos_origin(*file, e.lo);
            let (_, tr, selfty) = if (*parent as usize) < u.fns.len() && !matches!(u.fns[*parent as usize].key, FnKey::Closure(..)) {
                report_origin(u, &u.fns[*parent as usize].key)
            } else {
                ("-", String::new(), String::new())
            };
            (origin, tr, selfty)
        }
        FnKey::Shim(_) | FnKey::Glue(..) | FnKey::Sandbox(_) => ("-", String::new(), String::new()),
    }
}

/// The workspace (dirs.rs): RELAX_WORKSPACE, else the current folder.
pub fn workspace_dir() -> String {
    crate::dirs::workspace_dir()
}

#[cfg(test)]
mod settle_tests {
    use super::SettleWatch;

    #[test]
    fn settle_waits_for_present_and_quiet_then_rearms_after_a_burst() {
        let mut w = SettleWatch::default();
        let sec = 1_000_000_000;
        assert!(!w.ready(sec, 0, 0));
        assert!(!w.ready(2 * sec, 0, 10));
        assert!(!w.ready(3 * sec, 3 * sec, 10));
        assert!(w.ready(4 * sec, 3 * sec, 10));
        w.settled = Some(10);
        assert!(!w.ready(8 * sec, sec, 10));
        assert!(!w.ready(9 * sec, sec, 11));
        assert!(w.ready(10 * sec, sec, 11));
    }
}

/// The memory-throttled compile mode (mobile; local/plans/memory-use.md): RELAX_MEM_BUDGET_MB set.
/// Desktop default: unset, full parallelism -- the cold preload then runs ahead over all crates
/// and write-then-map only frees each crate's front end after its load.
fn mem_budget_mode() -> bool {
    std::env::var("RELAX_MEM_BUDGET_MB").map_or(false, |v| v.parse::<u64>().map_or(false, |n| n > 0))
}
