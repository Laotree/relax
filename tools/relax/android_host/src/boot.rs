//! Boot the host: compile a package's exported functions with Relax and publish their addresses.
//! No platform code here, so the Linux probe (examples/probe.rs) runs the same path as the phone.

use std::path::PathBuf;
use std::sync::Mutex;

/// Where the package's source comes from.
pub enum Source {
    /// The current directory is a checkout (the Linux probe).
    Checkout,
    /// A packed source archive (`relax pack-src`) at a byte range of a file: the APK's asset.
    Archive { file: PathBuf, offset: u64, len: u64 },
}

pub struct Boot {
    pub package: String,
    /// cargo flags after the package (`--no-default-features`, `--features ..`)
    pub cargo_flags: Vec<String>,
    /// symbol prefixes of the functions to compile and publish
    pub exports: Vec<String>,
    pub source: Source,
    /// Relax's own executable: what build scripts run as
    pub exe: PathBuf,
}

/// What the Activity shows while the host boots.
#[derive(Clone, Default)]
pub struct Status {
    /// "starting", "booting", "ready", "failed"
    pub state: &'static str,
    /// the last boot phase Relax finished ("unit graph", "build scripts", ...)
    pub phase: String,
    /// crates loaded of crates in the program
    pub loaded: u32,
    pub total: u32,
    pub error: String,
}

static STATUS: Mutex<Option<Status>> = Mutex::new(None);

pub fn set_state(state: &'static str, error: String) {
    let mut s = STATUS.lock().unwrap();
    let st = s.get_or_insert_with(Status::default);
    st.state = state;
    st.error = error;
}

/// The current status; while booting, Relax's progress is read at the call.
pub fn status() -> Status {
    let mut st = STATUS.lock().unwrap().clone().unwrap_or(Status { state: "starting", ..Status::default() });
    if st.state == "booting" {
        let (phase, loaded, total) = relax_compiler::run::progress();
        st.phase = phase;
        st.loaded = loaded;
        st.total = total;
    }
    st
}

/// The compile-memory budget for this device (RELAX_MEM_BUDGET_MB): the smaller of a quarter of the
/// physical RAM and 60% of what is available, at least 256 MB (/proc/meminfo).
pub fn memory_budget_mb() -> Option<u64> {
    let text = std::fs::read_to_string("/proc/meminfo").ok()?;
    let kb = |key: &str| -> Option<u64> { text.lines().find(|l| l.starts_with(key))?.split_whitespace().nth(1)?.parse().ok() };
    let (total, available) = (kb("MemTotal:")? / 1024, kb("MemAvailable:")? / 1024);
    Some((total / 4).min(available * 6 / 10).max(256))
}

/// Compiles the package's exported functions (Relax `run --exports`) and returns (symbol, address).
/// Runs on the boot thread: it holds the compiler's allocation zone while Relax loads the program.
pub fn boot(b: &Boot) -> Result<Vec<(String, u64)>, String> {
    let _zone = relax_compiler::zone_alloc::compiler();
    relax_compiler::clock::mark_process_start();
    relax::init_embedded(&b.exe);
    set_state("booting", String::new());
    let opts = vec!["--exports".to_string(), b.exports.join(",")];
    let mut rest = vec![b.package.clone()];
    rest.extend(b.cargo_flags.iter().cloned());
    let code = match &b.source {
        Source::Checkout => relax::run_checkout(opts, rest),
        Source::Archive { file, offset, len } => {
            let workspace = relax::mount_archive(file, *offset, *len)?;
            relax::run_mounted(&workspace, opts, rest)
        }
    };
    if code != 0 {
        return Err(format!("Relax could not boot {} (status {code}); see the log", b.package));
    }
    Ok(relax_compiler::run::exports())
}
