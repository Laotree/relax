//! The permanent window of `relax run`. Session 0 presents the boot document on
//! macOS and a theme-colour clear elsewhere; compilation and app domains are guests.
//! Only ending the run closes the physical window.
use crate::boot_progress::{History, Progress};
#[cfg(not(target_os = "macos"))]
use clear_window::HostWindow;
use makepad_hal::{domain_stop, open_flags, session::HOST, CmdWriter, Hal, Id, OpenReq};
#[cfg(target_os = "macos")]
use relax_boot::{Action, Boot as HostWindow, Document};
use relax_compiler::{
    diag::Diagnostic,
    domain::{AppSpec, DomainState},
    run_state::{self, Mode, ParkedPanic, Phase, State},
};
#[cfg(target_os = "macos")]
use std::sync::Condvar;
use std::{
    collections::{HashSet, VecDeque},
    path::PathBuf,
    sync::{
        atomic::{AtomicBool, AtomicI32, Ordering},
        Mutex, MutexGuard,
    },
    time::{Duration, Instant},
};

struct Run {
    window: Id,
    spec: Option<AppSpec>,
    domain: u32,
    pending: bool,
    stopping: bool,
    relaunch: Option<Instant>,
    baseline: u64,
    initial_failed: bool,
    #[cfg(target_os = "macos")]
    retry: bool,
}

enum Update {
    Compiler(run_state::Event),
    Domain(DomainState),
    Begin { warm: bool },
    Failure(String),
    #[cfg(target_os = "macos")]
    Message(String),
    #[cfg(target_os = "macos")]
    SourcesChanged,
}

enum Work {
    Save(PathBuf, String),
    #[cfg(target_os = "macos")]
    Resume {
        panic: String,
        choice: String,
        value: String,
    },
}

static RUN: Mutex<Option<Run>> = Mutex::new(None);
#[cfg(target_os = "macos")]
static RETRY: Condvar = Condvar::new();
static UPDATES: Mutex<VecDeque<Update>> = Mutex::new(VecDeque::new());
static PUMP: Mutex<Option<std::thread::JoinHandle<()>>> = Mutex::new(None);
static QUIT: AtomicBool = AtomicBool::new(false);
static PANICS_CHANGED: AtomicBool = AtomicBool::new(false);
static EXIT: AtomicI32 = AtomicI32::new(0);

fn state() -> MutexGuard<'static, Option<Run>> {
    RUN.lock().unwrap_or_else(|e| e.into_inner())
}

fn post(update: Update) {
    let _kept = relax_compiler::zone_alloc::kept();
    UPDATES
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .push_back(update);
    Hal::global().wake_session(HOST);
}

fn panic_changed() {
    PANICS_CHANGED.store(true, Ordering::Release);
    Hal::global().wake_session(HOST);
}

pub fn run(mut compile: Box<dyn FnMut() -> i32 + Send>) -> i32 {
    makepad_hal::expect_main_loop();
    let thread = std::thread::Builder::new()
        .name("relax-compile".into())
        .stack_size(8 << 20)
        .spawn(move || {
            let _compiler = relax_compiler::zone_alloc::compiler_thread();
            loop {
                let code = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| compile()))
                    .unwrap_or(101);
                let mut guard = state();
                let Some(run) = guard.as_mut() else {
                    EXIT.store(code, Ordering::Release);
                    QUIT.store(true, Ordering::Release);
                    makepad_hal::stop_main_loop();
                    return;
                };
                if code == 0 && run.spec.is_some() {
                    return;
                }
                if QUIT.load(Ordering::Acquire) {
                    return;
                }
                EXIT.store(code, Ordering::Release);
                #[cfg(not(target_os = "macos"))]
                {
                    // The clear-only host has no retry UI: retain M4a's exit behaviour.
                    QUIT.store(true, Ordering::Release);
                    Hal::global().wake_session(HOST);
                    if PUMP.lock().unwrap_or_else(|e| e.into_inner()).is_none() {
                        makepad_hal::stop_main_loop();
                    }
                    return;
                }
                #[cfg(target_os = "macos")]
                {
                    // With a unit already installed, retries go through domain relaunch.
                    run.initial_failed = run.spec.is_none();
                    post(Update::Failure(format!("Compilation failed (exit {code})")));
                    if run.spec.is_some() {
                        return;
                    }
                    while !QUIT.load(Ordering::Acquire) && !guard.as_ref().is_some_and(|r| r.retry) {
                        guard = RETRY.wait(guard).unwrap_or_else(|e| e.into_inner());
                    }
                    if QUIT.load(Ordering::Acquire) {
                        return;
                    }
                    if let Some(run) = guard.as_mut() {
                        run.retry = false;
                        run.initial_failed = false;
                    }
                    drop(guard);
                    post(Update::Begin { warm: false });
                }
            }
        })
        .expect("the compiler thread");
    {
        let _kept = relax_compiler::zone_alloc::kept();
        makepad_hal::run_main_loop();
    }
    QUIT.store(true, Ordering::Release);
    #[cfg(target_os = "macos")]
    RETRY.notify_all();
    Hal::global().wake_session(HOST);
    if thread.join().is_err() {
        return 101;
    }
    if let Some(pump) = PUMP.lock().unwrap_or_else(|e| e.into_inner()).take() {
        if pump.join().is_err() {
            return 101;
        }
    }
    EXIT.load(Ordering::Acquire)
}

#[cfg(target_os = "macos")]
fn document(package_dir: &str) -> Result<Document, String> {
    let manifest = format!("{package_dir}/Cargo.toml");
    let text =
        relax_compiler::vfs::read_to_string(&manifest).map_err(|e| format!("{manifest}: {e}"))?;
    let manifest = relax_compiler::toml::parse_toml(&text).map_err(|e| e.to_string())?;
    let Some(value) = manifest.get_path(&["package", "metadata", "makepad", "bootloader"]) else {
        let mut document = Document::bundled();
        if let Ok(source) = relax_compiler::vfs::read_to_string(&document.path) {
            document.source = source.into();
        }
        return Ok(document);
    };
    let relative = value
        .as_str()
        .filter(|s| !s.is_empty())
        .ok_or("package.metadata.makepad.bootloader must name a Splash document")?;
    let path = PathBuf::from(package_dir).join(relative);
    let source = relax_compiler::vfs::read_to_string(&path)
        .map_err(|e| format!("{}: {e}", path.display()))?;
    Ok(Document {
        path,
        source: source.into(),
    })
}

/// Called after graph resolution, before build scripts or application sources.
pub fn open(package: &str, _package_dir: &str) -> Result<(), String> {
    if state().is_some() {
        return Ok(());
    }
    let _kept = relax_compiler::zone_alloc::kept();
    let hal = Hal::global();
    let remote = relax_compiler::os::proc::args_bytes()
        .iter()
        .any(|a| a == b"--remote")
        || std::env::var_os("MAKEPAD_REMOTE").is_some();
    let flags = open_flags::RETAIN_WINDOWS
        | if cfg!(target_os = "macos") {
            open_flags::HIDDEN_UNTIL_PRESENT
        } else {
            0
        }
        | if remote { open_flags::NO_FOCUS } else { 0 };
    let info = hal.open_host(&OpenReq::from_env(0, flags, 0.0));
    if info.backend == makepad_hal::backend_id::NONE {
        return Err("could not open the host HAL session".into());
    }
    let key = package
        .as_bytes()
        .iter()
        .fold(0xcbf29ce484222325u64, |h, b| {
            (h ^ *b as u64).wrapping_mul(0x100000001b3)
        });
    let state_path = relax_compiler::dirs::relax_dir()
        .join("windows")
        .join(format!("{key:016x}.geom"));
    let geometry = std::fs::read_to_string(&state_path)
        .ok()
        .and_then(|s| {
            let values: Vec<f32> = s
                .split_whitespace()
                .map(str::parse)
                .collect::<Result<_, _>>()
                .ok()?;
            let g: [f32; 4] = values.try_into().ok()?;
            (g.iter().all(|v| v.is_finite()) && g[2] > 0.0 && g[3] > 0.0).then_some(g)
        })
        .unwrap_or([f32::NAN, f32::NAN, 1280.0, 800.0]);
    let history = History::load(
        relax_compiler::dirs::cache_dir()
            .join("boot")
            .join(format!("{key:016x}.timings")),
    );
    #[cfg(target_os = "macos")]
    let document = document(_package_dir).unwrap_or_else(|e| {
        post(Update::Message(e));
        Document::bundled()
    });
    *state() = Some(Run {
        window: Id::NONE,
        spec: None,
        domain: 0,
        pending: false,
        stopping: false,
        relaunch: None,
        baseline: 0,
        initial_failed: false,
        #[cfg(target_os = "macos")]
        retry: false,
    });
    run_state::set_observer(|event| post(Update::Compiler(event)));
    relax_compiler::tui::track_for_host();
    relax_compiler::inspect::events::set_run_state_observer(panic_changed);
    relax_compiler::inspect::events::run_state_available(cfg!(target_os = "macos"));
    let initial = State {
        app: package.into(),
        domain: "Compiling".into(),
        ..State::default()
    };
    #[cfg(target_os = "macos")]
    let package_dir = PathBuf::from(_package_dir);
    let (ready, first) = std::sync::mpsc::sync_channel(1);
    *PUMP.lock().unwrap_or_else(|e| e.into_inner()) = Some(
        std::thread::Builder::new()
            .name("relax-window".into())
            .stack_size(8 << 20)
            .spawn(move || {
                struct StopLoop;
                impl Drop for StopLoop {
                    fn drop(&mut self) {
                        makepad_hal::stop_main_loop();
                    }
                }
                let _stop = StopLoop;
                let _kept = relax_compiler::zone_alloc::kept();
                #[cfg(target_os = "macos")]
                let host = HostWindow::new(info, document, initial.clone(), geometry);
                #[cfg(not(target_os = "macos"))]
                let host = HostWindow::new(info.dpi, &initial.app, geometry);
                pump(
                    host,
                    initial,
                    history,
                    state_path,
                    #[cfg(target_os = "macos")]
                    package_dir,
                    ready,
                );
            })
            .map_err(|e| e.to_string())?,
    );
    first.recv().map_err(|e| e.to_string())?
}

pub fn start(spec: AppSpec) -> Result<(), String> {
    let _kept = relax_compiler::zone_alloc::kept();
    if QUIT.load(Ordering::Acquire) {
        return Err("run closed during compilation".into());
    }
    let launch =
        Hal::global().with_world(|w| w.start_domain(HOST, 0, spec.package.clone(), String::new()));
    {
        let mut state = state();
        let r = state.as_mut().ok_or("no host window")?;
        r.domain = launch.domain;
        r.spec = Some(spec);
    }
    relax_compiler::run::set_app_domain(launch.domain);
    crate::hal_host::start(launch)
}

pub fn spec(id: u32) -> Option<AppSpec> {
    state()
        .as_ref()
        .filter(|r| r.domain == id)
        .and_then(|r| r.spec.clone())
}

pub fn relaunch() -> Result<(), String> {
    let _kept = relax_compiler::zone_alloc::kept();
    let mut guard = state();
    let r = guard
        .as_mut()
        .filter(|r| r.domain != 0)
        .ok_or("the app has not started yet")?;
    if QUIT.load(Ordering::Acquire) {
        return Err("the run is closing".into());
    }
    if r.relaunch.is_none() {
        r.relaunch = Some(Instant::now());
        r.pending = true;
        r.stopping = true;
        post(Update::Begin { warm: true });
    }
    drop(guard);
    Hal::global().wake_session(HOST);
    Ok(())
}

pub fn restarting(id: u32) {
    let window = state()
        .as_ref()
        .filter(|r| r.domain == id)
        .map(|r| r.window);
    let Some(window) = window else { return };
    let baseline = Hal::global().with_world(|w| {
        w.session(HOST)
            .and_then(|s| s.windows.get(HOST, window).ok())
            .map_or(0, |w| w.val.presentations)
    });
    if let Some(r) = state().as_mut().filter(|r| r.domain == id) {
        if r.relaunch.is_none() {
            r.relaunch = Some(Instant::now());
            post(Update::Begin { warm: true });
        }
        r.stopping = false;
        r.baseline = baseline;
    }
}

pub fn observe(id: u32, next: &DomainState) {
    let guard = state();
    if let Some(r) = guard.as_ref().filter(|r| r.domain == id) {
        if !r.stopping || matches!(next, DomainState::Leaked { .. }) {
            post(Update::Domain(next.clone()));
        }
    }
}

#[cfg(target_os = "macos")]
fn retry() -> Result<(), String> {
    {
        let mut guard = state();
        let r = guard.as_mut().ok_or("no run window")?;
        if r.initial_failed {
            r.retry = true;
            RETRY.notify_one();
            return Ok(());
        }
    }
    relaunch()
}

fn work(
    rx: std::sync::mpsc::Receiver<Work>,
    #[cfg(target_os = "macos")] package_dir: PathBuf,
    #[cfg(target_os = "macos")] document: relax_boot::DocumentUpdates,
) {
    let _kept = relax_compiler::zone_alloc::kept();
    #[cfg(target_os = "macos")]
    let _document_watcher = document.watch();
    #[cfg(target_os = "macos")]
    let _source_watcher = if package_dir.is_dir() {
        use makepad_filesystem_watcher::{FileSystemWatcher, WatchRoot};
        FileSystemWatcher::start(
            vec![WatchRoot {
                mount: "run".into(),
                path: package_dir,
            }],
            |event| {
                if matches!(
                    event.path.extension().and_then(|e| e.to_str()),
                    Some("rs" | "toml")
                ) {
                    post(Update::SourcesChanged);
                }
            },
        )
        .map_err(|e| eprintln!("relax: source retry watcher: {e}"))
        .ok()
    } else {
        None
    };
    for work in rx {
        match work {
            Work::Save(path, text) => {
                if let Err(e) = crate::boot_progress::save(&path, &text) {
                    eprintln!("relax: cannot remember {}: {e}", path.display());
                }
            }
            #[cfg(target_os = "macos")]
            Work::Resume {
                panic,
                choice,
                value,
            } => {
                // Reuse inspect's validation and its domain-restart / restartable-fn logic.
                let (reply, _) = makepad_remote::cmd::answer(
                    relax_compiler::inspect::events::cmd_resume,
                    &format!("resume {panic} {choice} {value} full=1"),
                );
                for line in reply.split(|b| *b == b'\n') {
                    if let Ok(json) = relax_compiler::json::parse(line) {
                        if let Some(error) = json.get("err") {
                            post(Update::Message(error.str().into()));
                        }
                    }
                }
                panic_changed();
            }
        }
    }
}

fn parked(domain: u32) -> Option<Option<ParkedPanic>> {
    for event in relax_compiler::inspect::events::parked_events(domain)? {
        let Ok(json) = relax_compiler::json::parse(event.as_bytes()) else {
            continue;
        };
        let Some(id) = json.get("id") else { continue };
        let id = id.str().to_string();
        let choices = json
            .get("more")
            .map(|j| j.arr())
            .unwrap_or(&[])
            .iter()
            .filter_map(|j| {
                let mut words = j.str().split_whitespace();
                (words.next() == Some("resume") && words.next() == Some(id.as_str()))
                    .then(|| words.next().map(str::to_string))
                    .flatten()
            })
            .collect();
        return Some(Some(ParkedPanic {
            id,
            message: json.get("message").map_or("", |j| j.str()).into(),
            location: json.get("location").map_or("", |j| j.str()).into(),
            choices,
        }));
    }
    Some(None)
}

fn enqueue(queue: &mut VecDeque<Work>, work: Work) {
    // Geometry/timings are snapshots; a pending write of the same path can take
    // the newer value. User actions retain their order and are never dropped.
    match &work {
        Work::Save(path, text) => {
            for pending in queue.iter_mut().rev() {
                match pending {
                    Work::Save(old_path, old_text) if old_path == path => {
                        old_text.clone_from(text);
                        return;
                    }
                    _ => {}
                }
            }
        }
        #[cfg(target_os = "macos")]
        Work::Resume { .. } => {}
    }
    queue.push_back(work);
}

fn pump(
    mut host: HostWindow,
    mut data: State,
    history: History,
    geometry_path: PathBuf,
    #[cfg(target_os = "macos")] package_dir: PathBuf,
    ready: std::sync::mpsc::SyncSender<Result<(), String>>,
) {
    let hal = Hal::global();
    let (send, recv) = std::sync::mpsc::sync_channel(1);
    #[cfg(target_os = "macos")]
    let document = host.document_updates();
    let worker = std::thread::Builder::new()
        .name("relax-run-actions".into())
        .spawn(move || {
            work(
                recv,
                #[cfg(target_os = "macos")]
                package_dir,
                #[cfg(target_os = "macos")]
                document,
            )
        })
        .expect("run action worker");
    let mut work_pending = VecDeque::new();
    let mut work_full = false;
    let mut ready = Some(ready);
    let mut progress = Progress::new(history);
    let mut failed = false;
    let mut patch_failed = false;
    let mut overlay_dismissed = false;
    let mut active = true;
    let mut relaunched = false;
    let mut restartable = true;
    let mut diagnostics = Vec::new();
    let mut diagnostic_keys = HashSet::new();
    let mut diagnostics_dirty = true;
    #[cfg(target_os = "macos")]
    let mut document_errors = Vec::new();
    let mut saved_geometry = None;
    let mut next_frame = Instant::now();
    let mut next_status = Instant::now();
    let mut dirty = true;
    loop {
        let (domain, window, relaunch, baseline, pending, stopping, initial_failed) = {
            let mut guard = state();
            let r = guard.as_mut().expect("host run");
            (
                r.domain,
                r.window,
                r.relaunch,
                r.baseline,
                std::mem::take(&mut r.pending),
                r.stopping,
                r.initial_failed,
            )
        };
        if QUIT.load(Ordering::Acquire) {
            break;
        }
        if pending {
            let mut cmd = CmdWriter::new(HOST);
            if !window.is_none() { cmd.window_overlay(window, false, [0.0; 4]); }
            cmd.domain_relaunch(domain);
            hal.submit(&cmd.buf());
        }
        let updates = std::mem::take(&mut *UPDATES.lock().unwrap_or_else(|e| e.into_inner()));
        for update in updates {
            dirty = true;
            match update {
                Update::Begin { warm } => {
                    progress.reset();
                    data.phase = Phase::Resolve;
                    data.done = None;
                    data.total = None;
                    data.current.clear();
                    data.warm = warm;
                    data.progress = 0.0;
                    data.parked = None;
                    data.domain = "Compiling".into();
                    diagnostics.clear();
                    diagnostic_keys.clear();
                    diagnostics_dirty = true;
                    failed = false;
                    patch_failed = false;
                    overlay_dismissed = false;
                    active = true;
                    relaunched |= warm;
                    restartable = true;
                }
                Update::Failure(message) => {
                    diagnostics.push(Diagnostic::new("run", "", 0, 0, message));
                    diagnostics_dirty = true;
                    failed = true;
                    active = false;
                    data.domain = "Boot failed".into();
                    if let Some(r) = state().as_mut() {
                        r.relaunch = None;
                        r.stopping = false;
                    }
                }
                #[cfg(target_os = "macos")]
                Update::Message(message) => {
                    diagnostics.push(Diagnostic::new("run", "", 0, 0, message));
                    diagnostics_dirty = true;
                }
                #[cfg(target_os = "macos")]
                Update::SourcesChanged => {
                    if failed && !stopping && restartable {
                        match retry() {
                            Ok(()) => failed = false,
                            Err(e) => post(Update::Message(e)),
                        }
                    }
                }
                Update::Domain(next) => match next {
                    DomainState::Compiling(name) => {
                        let phase = match name.as_str() {
                            "loading crates" | "load" => Phase::Parse,
                            "collect" => Phase::Typecheck,
                            "link" => Phase::Link,
                            "main" => Phase::Codegen,
                            _ => Phase::Resolve,
                        };
                        progress.phase(phase);
                        data.phase = phase;
                        data.done = None;
                        data.total = None;
                        data.current = name;
                        data.domain = "Compiling".into();
                    }
                    DomainState::Running => {
                        data.domain = "Starting".into();
                        progress.phase(Phase::FirstFrame);
                        data.phase = Phase::FirstFrame;
                        data.done = None;
                        data.total = None;
                    }
                    DomainState::Exited(code) if code == 0 || !cfg!(target_os = "macos") => {
                        EXIT.store(code, Ordering::Release);
                        QUIT.store(true, Ordering::Release);
                    }
                    DomainState::Exited(code) => {
                        post(Update::Failure(format!("App exited with status {code}")))
                    }
                    DomainState::Crashed(message) => post(Update::Failure(message)),
                    DomainState::Leaked { threads } => {
                        post(Update::Failure(format!(
                            "Shutdown timed out: {threads} threads remain"
                        )));
                        restartable = false;
                    }
                    DomainState::Stopped => {}
                },
                Update::Compiler(event) => match event {
                    run_state::Event::Progress {
                        domain: id,
                        phase,
                        done,
                        total,
                        item,
                    } if id.is_none() || id == Some(domain) => {
                        progress.phase(phase);
                        data.phase = phase;
                        data.done = done;
                        data.total = total;
                        data.current = item;
                    }
                    run_state::Event::Warm { domain: id, warm }
                        if id.is_none() || (id == Some(domain) && relaunched) =>
                    {
                        data.warm = warm
                    }
                    run_state::Event::Diagnostic { domain: id, record }
                        if id.is_none() || id == Some(domain) =>
                    {
                        if diagnostic_keys.insert(record.to_json()) {
                            if !active && record.severity == relax_compiler::diag::Severity::Error {
                                patch_failed = true;
                                overlay_dismissed = false;
                            }
                            diagnostics.push(record);
                            diagnostics_dirty = true;
                        }
                    }
                    run_state::Event::Patch {
                        domain: id,
                        applied,
                        records,
                    } if id.is_none() || id == Some(domain) => {
                        patch_failed = !applied;
                        overlay_dismissed = applied;
                        diagnostic_keys = records.iter().map(Diagnostic::to_json).collect();
                        diagnostics = records.to_vec();
                        diagnostics_dirty = true;
                    }
                    _ => {}
                },
            }
        }
        if QUIT.load(Ordering::Acquire) {
            break;
        }
        if PANICS_CHANGED.swap(false, Ordering::AcqRel) {
            if let Some(parked) = parked(domain) {
                if data.parked.as_ref().map(|p| &p.id) != parked.as_ref().map(|p| &p.id) {
                    overlay_dismissed = parked.is_none();
                }
                data.parked = parked;
                dirty = true;
            } else {
                PANICS_CHANGED.store(true, Ordering::Release);
            }
        }
        let physical = hal.with_world(|w| {
            w.session(HOST)
                .and_then(|s| s.windows.get(HOST, window).ok())
                .map(|w| {
                    (
                        w.val.geom,
                        w.val.borrower_frame,
                        w.val.presentations,
                        w.val.presenter,
                        w.lent_to,
                    )
                })
        });
        let mut may_present = true;
        let mut app_frame = false;
        if let Some((geom, borrower_frame, presentations, presenter, lent)) = physical {
            app_frame = borrower_frame && lent == domain && domain != 0 && !stopping && !pending;
            may_present = if cfg!(target_os = "macos") {
                !borrower_frame || lent == 0
            } else {
                presentations == 0 && lent == 0
            };
            if saved_geometry != Some(geom)
                && geom.iter().all(|v| v.is_finite())
                && geom[2] > 0.0
                && geom[3] > 0.0
            {
                saved_geometry = Some(geom);
                enqueue(
                    &mut work_pending,
                    Work::Save(
                        geometry_path.clone(),
                        format!("{} {} {} {}\n", geom[0], geom[1], geom[2], geom[3]),
                    ),
                );
            }
            if presentations > 0 {
                if let Some(ready) = ready.take() {
                    let _ = ready.try_send(Ok(()));
                }
            }
            if active
                && borrower_frame
                && lent == domain
                && !pending
                && !stopping
                && domain != 0
                && presenter == domain
                && presentations > baseline
            {
                active = false;
                failed = false;
                data.progress = 1.0;
                data.domain = "Running".into();
                EXIT.store(0, Ordering::Release);
                let (path, contents) = progress.finish(data.warm);
                enqueue(&mut work_pending, Work::Save(path, contents));
                if let Some(r) = state().as_mut() {
                    if let Some(t) = r.relaunch.take() {
                        eprintln!(
                            "relaunch: {:.1} ms to first frame (window kept)",
                            t.elapsed().as_secs_f64() * 1000.0
                        );
                    }
                }
                dirty = true;
            }
        }
        // Errors reveal immediately. Otherwise a warm relaunch preserves the last app
        // image for 300 ms, then uses exactly the same document/context as cold boot.
        let overlay = cfg!(target_os = "macos") && app_frame && !overlay_dismissed
            && (patch_failed || data.parked.is_some());
        let mode = if overlay { Mode::Overlay } else { Mode::Boot };
        if data.mode != mode { data.mode = mode; dirty = true; }
        let visible = overlay || (cfg!(target_os = "macos")
            && may_present
            && (failed
                || data.parked.is_some()
                || (active && relaunch.is_none_or(|t| t.elapsed() >= Duration::from_millis(300)))));
        if active && Instant::now() >= next_status {
            progress.tick(&mut data);
            if matches!(data.phase, Phase::Codegen | Phase::FirstFrame) {
                if let Some(item) = relax_compiler::tui::current_item() {
                    data.current = item;
                }
            }
            next_status = Instant::now() + Duration::from_millis(100);
            dirty = true;
        }
        if diagnostics_dirty {
            let records = diagnostics.iter().cloned();
            #[cfg(target_os = "macos")]
            let records = records.chain(document_errors.iter().cloned());
            data.diagnostics = records.collect::<Vec<_>>().into();
            diagnostics_dirty = false;
            dirty = true;
        }
        if dirty {
            data.can_retry = restartable && (initial_failed || (failed && domain != 0));
            data.can_restart = restartable && domain != 0 && !stopping;
            #[cfg(target_os = "macos")]
            host.update(data.clone());
            dirty = false;
        }
        let draw = visible && Instant::now() >= next_frame;
        let timeout = if visible {
            next_frame
                .saturating_duration_since(Instant::now())
                .as_nanos() as u64
        } else if (cfg!(target_os = "macos") && active)
            || !work_pending.is_empty()
            || PANICS_CHANGED.load(Ordering::Acquire)
        {
            16_666_667
        } else {
            u64::MAX
        };
        let alive = host.turn(timeout, draw || (!cfg!(target_os = "macos") && may_present));
        if window.is_none() {
            if let Some(window) = host.window() {
                if let Some(r) = state().as_mut() {
                    r.window = window;
                }
            }
        }
        if !alive {
            QUIT.store(true, Ordering::Release);
            break;
        }
        if draw {
            next_frame = Instant::now() + Duration::from_nanos(16_666_667);
        }
        #[cfg(target_os = "macos")]
        for action in host.actions() {
            match action {
                Action::Dismiss => {
                    overlay_dismissed = true;
                    dirty = true;
                }
                Action::RetryCompile | Action::RestartDomain => match retry() {
                    Ok(()) => failed = false,
                    Err(e) => post(Update::Message(e)),
                },
                Action::Resume {
                    panic,
                    choice,
                    value,
                } => work_pending.push_back(Work::Resume {
                    panic,
                    choice,
                    value,
                }),
                Action::Copy(text) => host.copy(&text),
                Action::OpenFile { file, line, col } => {
                    if let Err(e) = host.open_file(file, line, col) {
                        post(Update::Message(e));
                    }
                }
                Action::DocumentErrors(errors) => {
                    document_errors = errors;
                    diagnostics_dirty = true;
                }
            }
        }
        while let Some(work) = work_pending.pop_front() {
            match send.try_send(work) {
                Ok(()) => {
                    work_full = false;
                }
                Err(std::sync::mpsc::TrySendError::Full(work)) => {
                    if !work_full {
                        eprintln!(
                            "relax: run action worker busy; retaining work for a later frame"
                        );
                        work_full = true;
                    }
                    work_pending.push_front(work);
                    break;
                }
                Err(std::sync::mpsc::TrySendError::Disconnected(work)) => {
                    work_pending.push_front(work);
                    eprintln!("relax: run action worker stopped; closing the run");
                    EXIT.store(101, Ordering::Release);
                    QUIT.store(true, Ordering::Release);
                    break;
                }
            }
        }
    }
    relax_compiler::inspect::events::run_state_available(false);
    #[cfg(target_os = "macos")]
    RETRY.notify_all();
    if let Some(ready) = ready {
        let _ = ready.try_send(Err("run closed before its first frame".into()));
    }
    let (domain, window) = state()
        .as_ref()
        .map_or((0, Id::NONE), |r| (r.domain, r.window));
    let mut cmd = CmdWriter::new(HOST);
    if domain != 0 {
        cmd.domain_stop(domain, domain_stop::QUIT);
    }
    if !window.is_none() {
        cmd.window_close(window);
    }
    hal.submit(&cmd.buf());
    // The UI has stopped: finish pending persistence/actions before ending this run.
    for work in work_pending {
        let _ = send.send(work);
    }
    drop(send);
    if worker.join().is_err() {
        eprintln!("relax: run action worker panicked");
    }
}

/// Until another platform migrates its client, keep the M4a presenter: one
/// theme-colour clear, then let the physical window retain the app's last frame.
#[cfg(not(target_os = "macos"))]
mod clear_window {
    use makepad_hal::{
        lifecycle, pass_load, session::HOST, target, window_kind, CmdWriter, EventStore, FrameMeta,
        Hal, HalEvent, Id, Pass,
    };

    pub(super) struct HostWindow {
        window: Id,
        events: EventStore,
        geometry: [f32; 4],
        dpi: f32,
        frame: u64,
        dirty: bool,
        color: [f32; 4],
    }

    impl HostWindow {
        pub(super) fn new(dpi: f32, title: &str, geometry: [f32; 4]) -> Self {
            let hal = Hal::global();
            let window = hal.with_world(|w| w.host_window(geometry));
            let mut cmd = CmdWriter::new(HOST);
            cmd.window_create(window, window_kind::NORMAL, Id::NONE, geometry, false);
            cmd.str_def(1, title.as_bytes());
            cmd.window_title(window, 1);
            hal.submit(&cmd.buf());
            Self {
                window,
                events: EventStore::new(HOST, 64, 65536),
                geometry,
                dpi,
                frame: 0,
                dirty: false,
                color: background(),
            }
        }

        pub(super) fn window(&mut self) -> Option<Id> {
            Some(self.window)
        }

        pub(super) fn turn(&mut self, timeout_ns: u64, present: bool) -> bool {
            let hal = Hal::global();
            let mut out = self.events.buf();
            let n = hal.pump(timeout_ns, &mut out);
            for (_, event) in self.events.reader(n, out.arena_len) {
                match event {
                    HalEvent::Geom {
                        window, x, y, w, h, dpi, ..
                    } if window == self.window => {
                        self.geometry = [x as f32, y as f32, w as f32, h as f32];
                        self.dpi = dpi;
                        self.dirty = true;
                    }
                    HalEvent::FrameDone { .. } => self.dirty = true,
                    HalEvent::FrameReady { window, .. } if window == self.window => {
                        self.dirty = true;
                    }
                    HalEvent::CloseRequested { window } | HalEvent::Closed { window }
                        if window == self.window =>
                    {
                        return false;
                    }
                    HalEvent::Lifecycle {
                        kind: lifecycle::QUIT_REQUESTED,
                    } => return false,
                    _ => {}
                }
            }
            if present && self.dirty {
                let may_clear = hal.with_world(|w| {
                    w.session(HOST)
                        .and_then(|s| s.windows.get(HOST, self.window).ok())
                        .is_some_and(|w| w.lent_to == 0 && w.val.presentations == 0)
                });
                if may_clear {
                    self.frame += 1;
                    let mut cmd = CmdWriter::new(HOST);
                    cmd.frame_begin(self.frame, FrameMeta::default());
                    cmd.pass(Pass {
                        viewport: [
                            0.0,
                            0.0,
                            self.geometry[2] * self.dpi,
                            self.geometry[3] * self.dpi,
                        ],
                        dpi: self.dpi,
                        load: [pass_load::CLEAR; 5],
                        clear: [self.color; 4],
                        clear_depth: 1.0,
                        ..Default::default()
                    });
                    cmd.frame_end(self.window, target::WINDOW);
                    hal.submit(&cmd.buf());
                }
                self.dirty = false;
            }
            true
        }
    }

    /// The default desktop theme's ground, or the launcher's literal theme ground.
    fn background() -> [f32; 4] {
        let sheet = std::env::var_os("MAKEPAD_WIDGET_STYLE_FILE")
            .and_then(|p| std::fs::read(p).ok())
            .and_then(|b| relax_compiler::json::parse(&b).ok())
            .and_then(|j| {
                j.get("makepad_style")?
                    .get("theme")
                    .map(|t| t.str().to_string())
            })
            .or_else(|| {
                let name = std::env::var("MAKEPAD_WIDGET_STYLE").ok()?;
                let path = format!(
                    "{}/widgets/themes/{name}/theme.splash",
                    relax_compiler::run::workspace_dir(),
                );
                relax_compiler::vfs::read_to_string(&path).ok()
            });
        sheet
            .and_then(|s| {
                s.lines().rev().find_map(|line| {
                    let hex = line
                        .trim()
                        .strip_prefix("mod.theme.color_bg_app")?
                        .trim_start()
                        .strip_prefix('=')?
                        .split("//")
                        .next()?
                        .trim()
                        .strip_prefix('#')?;
                    let hex = hex.strip_prefix('x').unwrap_or(hex);
                    let n = u32::from_str_radix(hex, 16).ok()?;
                    let rgba = match hex.len() {
                        6 => (n << 8) | 255,
                        8 => n,
                        _ => return None,
                    };
                    Some([
                        ((rgba >> 24) & 255) as f32 / 255.0,
                        ((rgba >> 16) & 255) as f32 / 255.0,
                        ((rgba >> 8) & 255) as f32 / 255.0,
                        (rgba & 255) as f32 / 255.0,
                    ])
                })
            })
            .unwrap_or([0.3, 0.3, 0.3, 1.0])
    }
}
