//! `relax host-gen [--check] [--verbose] [<package>...]`: the shim file (`src/host_shims.rs`) of
//! every crate this binary provides (or the ones named), the same on every machine. Each crate is
//! read once per target relax runs on (provided.rs HOST_GEN_TARGETS: a worker process per target,
//! RELAX_CHECK_TARGET), with the features this build compiles it with (build.rs
//! RELAX_PROVIDED), never the host's cfgs or a program's feature set; the targets' rows merge into
//! one file whose target-only rows are cfg-gated (provided.rs host_gen_file).
//! `--check` writes nothing: exit 1 when a file would change (the merge gate).

use std::process::{Command, Stdio};

fn usage() -> i32 {
    eprintln!("usage: relax host-gen [--check] [--verbose] [<package>...]");
    2
}

/// The provided packages and the features this build compiles each with.
fn provided() -> Vec<(&'static str, &'static str)> {
    env!("RELAX_PROVIDED").split(';').filter_map(|e| e.split_once('=')).collect()
}

/// The worker: `relax host-gen --worker <package> <rows file> [cargo flags]`, one target
/// (RELAX_CHECK_TARGET): the crate's rows for that target.
pub fn worker(args: &[String]) -> i32 {
    if args.len() < 2 {
        return usage();
    }
    let mut a = vec!["--check".to_string(), "--host-gen".to_string(), args[0].clone(), args[1].clone(), args[0].clone()];
    a.extend(args[2..].iter().cloned());
    let mut sess = relax_compiler::session_from_env(&std::env::args().collect::<Vec<_>>());
    // A shim table describes the whole crate, including modules no program calls yet.
    std::sync::Arc::get_mut(&mut sess).expect("new host-gen session").options.source_eager = true;
    relax_compiler::run::cmd_run(&sess, &a)
}

pub fn main(args: &[String]) -> i32 {
    let (mut check, mut verbose) = (false, false);
    let mut only: Vec<&str> = Vec::new();
    for a in args {
        match a.as_str() {
            "--check" => check = true,
            "--verbose" => verbose = true,
            x if x.starts_with('-') => return usage(),
            x => only.push(x),
        }
    }
    let all = provided();
    if let Some(x) = only.iter().find(|x| !all.iter().any(|(p, _)| p == *x)) {
        let names: Vec<&str> = all.iter().map(|(p, _)| *p).collect();
        eprintln!("relax host-gen: `{x}` is not a provided crate of this relax ({})", names.join(", "));
        return 2;
    }
    let Ok(exe) = std::env::current_exe() else {
        eprintln!("relax host-gen: no path to this executable");
        return 2;
    };
    let cwd = std::env::current_dir().map(|d| d.display().to_string()).unwrap_or_default();
    let discovery = std::sync::Arc::new(relax_compiler::Session::default());
    let mut stale = Vec::new();
    for (pkg, features) in all.iter().filter(|(p, _)| only.is_empty() || only.contains(p)) {
        let dir = match relax_compiler::resolve::package_dir(&discovery, &cwd, pkg) {
            Ok(d) => d,
            Err(e) => {
                eprintln!("relax host-gen: {pkg}: {e}");
                return 2;
            }
        };
        let out = format!("{dir}/src/host_shims.rs");
        let mut targets = Vec::new();
        let mut counts = Vec::new();
        for (triple, _) in relax_compiler::provided::HOST_GEN_TARGETS {
            let rows = std::env::temp_dir().join(format!("relax-host-gen-{}-{pkg}-{triple}.rows", std::process::id()));
            let mut c = Command::new(&exe);
            c.args(["host-gen", "--worker", pkg]).arg(&rows).arg("--no-default-features");
            if !features.is_empty() {
                c.args(["--features", features]);
            }
            c.env("RELAX_CHECK_TARGET", triple).stdin(Stdio::null()).stdout(Stdio::null()).stderr(Stdio::piped());
            let res = match c.output() {
                Ok(o) => o,
                Err(e) => {
                    eprintln!("relax host-gen: {pkg} ({triple}): {e}");
                    return 2;
                }
            };
            let report = String::from_utf8_lossy(&res.stderr).into_owned();
            let text = std::fs::read_to_string(&rows);
            let _ = std::fs::remove_file(&rows);
            let parsed = match (res.status.success(), text) {
                (true, Ok(t)) => relax_compiler::provided::rows_from_text(&t),
                (_, _) => Err(format!("worker failed ({})", res.status)),
            };
            match parsed {
                Ok(r) => targets.push(r),
                Err(e) => {
                    eprintln!("relax host-gen: {pkg} ({triple}): {e}\n{report}");
                    return 2;
                }
            }
            // the report's first line: "host-gen <crate>: <n> fns bound, <m> opaque types; .."
            let line = report.lines().find(|l| l.starts_with("host-gen ")).unwrap_or("");
            let n = line.split_once(": ").and_then(|(_, r)| r.split(' ').next()).unwrap_or("?");
            counts.push(format!("{triple} {n}"));
            if verbose {
                eprintln!("[{triple}] {}", report.trim_end());
            }
        }
        let text = relax_compiler::provided::host_gen_file(&targets);
        let same = std::fs::read(&out).is_ok_and(|old| old == text.as_bytes());
        let state = if same {
            "unchanged"
        } else if check {
            stale.push(out.clone());
            "STALE"
        } else {
            if let Err(e) = std::fs::write(&out, &text) {
                eprintln!("relax host-gen: {out}: {e}");
                return 2;
            }
            "written"
        };
        eprintln!("host-gen {pkg}: fns bound {} -> {out} {state}", counts.join(" / "));
    }
    if !stale.is_empty() {
        eprintln!("relax host-gen --check: {} shim file(s) differ from the source; run `relax host-gen` and commit them", stale.len());
        return 1;
    }
    0
}
