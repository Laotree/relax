//! The permanent window of `relax run`. Compilation and app domains are guests of this host;
//! only ending the run closes its window or stops the HAL's process main loop.

use makepad_hal::{domain_stop, lifecycle, open_flags, pass_load, session::HOST, target, window_kind, CmdWriter, EventStore, FrameMeta, Hal, HalEvent, Id, OpenReq, Pass};
use relax_compiler::domain::{AppSpec, DomainState};
use std::path::PathBuf;
use std::sync::{atomic::{AtomicBool, AtomicI32, Ordering}, Mutex, MutexGuard};
use std::time::Instant;

struct Run {
    window: Id,
    state_path: PathBuf,
    spec: Option<AppSpec>,
    domain: u32,
    pending: bool,
    stopping: bool,
    relaunch: Option<Instant>,
    baseline: u64,
    finished: Option<i32>,
}

static RUN: Mutex<Option<Run>> = Mutex::new(None);
static PUMP: Mutex<Option<std::thread::JoinHandle<()>>> = Mutex::new(None);
static QUIT: AtomicBool = AtomicBool::new(false);
static EXIT: AtomicI32 = AtomicI32::new(0);

fn state() -> MutexGuard<'static, Option<Run>> {
    RUN.lock().unwrap_or_else(|e| e.into_inner())
}

pub fn run(compile: Box<dyn FnOnce() -> i32 + Send>) -> i32 {
    makepad_hal::expect_main_loop();
    let thread = std::thread::Builder::new().name("relax-boot".into()).stack_size(8 << 20).spawn(move || {
        let _compiler = relax_compiler::zone_alloc::compiler_thread();
        let code = std::panic::catch_unwind(std::panic::AssertUnwindSafe(compile)).unwrap_or(101);
        if code != 0 || state().as_ref().is_none_or(|r| r.spec.is_none()) {
            EXIT.store(code, Ordering::Release);
            QUIT.store(true, Ordering::Release);
            Hal::global().wake_session(HOST);
            if PUMP.lock().unwrap_or_else(|e| e.into_inner()).is_none() { makepad_hal::stop_main_loop(); }
        }
        code
    }).expect("the compiler thread");
    {
        let _kept = relax_compiler::zone_alloc::kept();
        makepad_hal::run_main_loop();
    }
    QUIT.store(true, Ordering::Release);
    Hal::global().wake_session(HOST);
    let code = thread.join().unwrap_or(101);
    if let Some(pump) = PUMP.lock().unwrap_or_else(|e| e.into_inner()).take() {
        if pump.join().is_err() { return 101; }
    }
    if code != 0 { code } else { EXIT.load(Ordering::Acquire) }
}

/// Called after graph resolution, before any build scripts or app source are compiled.
pub fn open(package: &str) -> Result<(), String> {
    let _kept = relax_compiler::zone_alloc::kept();
    let hal = Hal::global();
    let remote = relax_compiler::os::proc::args_bytes().iter().any(|a| a == b"--remote") || std::env::var_os("MAKEPAD_REMOTE").is_some();
    let flags = open_flags::RETAIN_WINDOWS | if remote { open_flags::NO_FOCUS } else { 0 };
    let info = hal.open_host(&OpenReq::from_env(0, flags, 0.0));
    if info.backend == makepad_hal::backend_id::NONE { return Err("could not open the host HAL session".into()); }
    let key = package.as_bytes().iter().fold(0xcbf29ce484222325u64, |h, b| (h ^ *b as u64).wrapping_mul(0x100000001b3));
    let path = relax_compiler::dirs::relax_dir().join("windows").join(format!("{key:016x}.geom"));
    let geom = std::fs::read_to_string(&path).ok().and_then(|s| {
        let values: Vec<f32> = s.split_whitespace().map(str::parse).collect::<Result<_, _>>().ok()?;
        let g: [f32; 4] = values.try_into().ok()?;
        (g.iter().all(|v| v.is_finite()) && g[2] > 0.0 && g[3] > 0.0).then_some(g)
    }).unwrap_or([f32::NAN, f32::NAN, 1280.0, 800.0]);
    let window = hal.with_world(|w| w.host_window(geom));
    *state() = Some(Run { window, state_path: path, spec: None, domain: 0, pending: false, stopping: false, relaunch: None, baseline: 0, finished: None });
    let mut cmd = CmdWriter::new(HOST);
    cmd.window_create(window, window_kind::NORMAL, Id::NONE, geom, false);
    cmd.str_def(1, package.as_bytes());
    cmd.window_title(window, 1);
    hal.submit(&cmd.buf());
    let (ready, first) = std::sync::mpsc::sync_channel(1);
    *PUMP.lock().unwrap_or_else(|e| e.into_inner()) = Some(std::thread::Builder::new().name("relax-window".into()).spawn(move || {
        struct StopLoop;
        impl Drop for StopLoop {
            fn drop(&mut self) { makepad_hal::stop_main_loop(); }
        }
        let _stop = StopLoop;
        let _kept = relax_compiler::zone_alloc::kept();
        pump(window, info.dpi, ready);
    }).map_err(|e| e.to_string())?);
    first.recv().map_err(|e| e.to_string())?
}

pub fn start(spec: AppSpec) -> Result<(), String> {
    let _kept = relax_compiler::zone_alloc::kept();
    if QUIT.load(Ordering::Acquire) { return Err("run closed during compilation".into()); }
    let hal = Hal::global();
    let launch = hal.with_world(|w| w.start_domain(HOST, 0, spec.package.clone(), String::new()));
    {
        let mut state = state();
        let r = state.as_mut().ok_or("no host window")?;
        r.domain = launch.domain;
        r.spec = Some(spec);
    }
    relax_compiler::run::set_app_domain(launch.domain);
    crate::hal_host::start(launch)
}

/// The primary app preserves cargo flags and exact argv on every launch. Child domains use
/// the spec sent by their parent; both run through the same domain loader and HAL launch.
pub fn spec(id: u32) -> Option<AppSpec> {
    state().as_ref().filter(|r| r.domain == id).and_then(|r| r.spec.clone())
}

pub fn relaunch() -> Result<(), String> {
    let _kept = relax_compiler::zone_alloc::kept();
    let mut state = state();
    let r = state.as_mut().filter(|r| r.domain != 0).ok_or("the app has not started yet")?;
    if QUIT.load(Ordering::Acquire) { return Err("the run is closing".into()); }
    if r.relaunch.is_none() {
        r.relaunch = Some(Instant::now());
        r.pending = true;
        r.stopping = true;
        r.finished = None;
    }
    drop(state);
    Hal::global().wake_session(HOST);
    Ok(())
}

/// The old session is gone and the new domain has not been started yet.
pub fn restarting(id: u32) {
    let mut state = state();
    if let Some(r) = state.as_mut().filter(|r| r.domain == id) {
        r.relaunch.get_or_insert_with(Instant::now);
        r.stopping = false;
        r.baseline = Hal::global().with_world(|w| w.session(HOST).and_then(|s| s.windows.get(HOST, r.window).ok()).map_or(0, |w| w.val.presentations));
    }
}

pub fn observe(id: u32, next: &DomainState) {
    let mut state = state();
    if let Some(r) = state.as_mut().filter(|r| r.domain == id) {
        match next {
            DomainState::Exited(code) if !r.stopping => r.finished = Some(*code),
            DomainState::Crashed(_) | DomainState::Leaked { .. } if !r.stopping => {
                // Keep the last frame and the inspect endpoint, including after a failed retry.
                r.relaunch = None;
                r.pending = false;
            }
            _ => {}
        }
    }
    drop(state);
    Hal::global().wake_session(HOST);
}

fn pump(window: Id, mut dpi: f32, ready: std::sync::mpsc::SyncSender<Result<(), String>>) {
    let hal = Hal::global();
    let mut events = EventStore::new(HOST, 64, 65536);
    let mut ready = Some(ready);
    let mut geom = [0.0, 0.0, 1280.0, 800.0];
    let mut frame = 0;
    let mut dirty = false;
    let mut saved = None;
    let color = background();
    loop {
        let mut out = events.buf();
        let n = hal.pump(u64::MAX, &mut out);
        let mut geometry = None;
        for (_, event) in events.reader(n, out.arena_len) {
            match event {
                HalEvent::Geom { window: w, x, y, w: width, h, dpi: scale, .. } if w == window => {
                    geom = [x as f32, y as f32, width as f32, h as f32];
                    dpi = scale;
                    geometry = Some(geom);
                    dirty = true;
                }
                HalEvent::FrameDone { .. } => dirty |= ready.is_some(),
                HalEvent::FrameReady { window: w, .. } if w == window => dirty = true,
                HalEvent::CloseRequested { window: w } | HalEvent::Closed { window: w } if w == window => QUIT.store(true, Ordering::Release),
                HalEvent::Lifecycle { kind: lifecycle::QUIT_REQUESTED } => QUIT.store(true, Ordering::Release),
                _ => {}
            }
        }
        if let Some(g) = geometry.filter(|g| g.iter().all(|v| v.is_finite()) && g[2] > 0.0 && g[3] > 0.0 && saved != Some(*g)) {
            let path = state().as_ref().expect("host run").state_path.clone();
            let result = std::fs::create_dir_all(path.parent().expect("state folder")).and_then(|_| {
                let pending = path.with_extension("pending");
                std::fs::write(&pending, format!("{} {} {} {}\n", g[0], g[1], g[2], g[3]))?;
                std::fs::rename(pending, &path)
            });
            match result {
                Ok(()) => saved = Some(g),
                Err(e) => eprintln!("relax: cannot remember window geometry: {e}"),
            }
        }
        let pending = {
            let mut state = state();
            let r = state.as_mut().expect("host run");
            if let Some(code) = r.finished { EXIT.store(code, Ordering::Release); QUIT.store(true, Ordering::Release); }
            std::mem::take(&mut r.pending).then_some(r.domain)
        };
        if QUIT.load(Ordering::Acquire) { break; }
        if let Some(id) = pending {
            let mut cmd = CmdWriter::new(HOST);
            cmd.domain_relaunch(id);
            hal.submit(&cmd.buf());
        }
        let (lent, presentations, presenter) = hal.with_world(|w| {
            let window = w.session(HOST).and_then(|s| s.windows.get(HOST, window).ok());
            window.map_or((true, 0, 0), |w| (w.lent_to != 0, w.val.presentations, w.val.presenter))
        });
        if presentations != 0 {
            if let Some(ready) = ready.take() { let _ = ready.send(Ok(())); }
        }
        {
            let mut state = state();
            let r = state.as_mut().expect("host run");
            if !r.pending && presenter == r.domain && presentations > r.baseline {
                if let Some(t) = r.relaunch.take() {
                    eprintln!("relaunch: {:.1} ms to first frame (window kept)", t.elapsed().as_secs_f64() * 1000.0);
                }
            }
        }
        // The uniform boot clear scales with the layer during compilation. After its first
        // presentation the host submits no more frames: the layer keeps the app's last image
        // through resize, detach, compilation and adoption, including late GPU completions.
        if dirty && !lent && presentations == 0 {
            frame += 1;
            let mut cmd = CmdWriter::new(HOST);
            cmd.frame_begin(frame, FrameMeta::default());
            cmd.pass(Pass { viewport: [0.0, 0.0, geom[2] * dpi, geom[3] * dpi], dpi, load: [pass_load::CLEAR; 5], clear: [color; 4], clear_depth: 1.0, ..Default::default() });
            cmd.frame_end(window, target::WINDOW);
            hal.submit(&cmd.buf());
            dirty = false;
        }
    }
    if let Some(ready) = ready { let _ = ready.send(Err("run closed before its first frame".into())); }
    let domain = state().as_ref().map_or(0, |r| r.domain);
    let mut cmd = CmdWriter::new(HOST);
    if domain != 0 { cmd.domain_stop(domain, domain_stop::QUIT); }
    hal.submit(&cmd.buf());
    let mut cmd = CmdWriter::new(HOST);
    cmd.window_close(window);
    hal.submit(&cmd.buf());
}

/// The default desktop theme's ground, or the literal ground in the launcher's style sheet.
/// M4b will evaluate the whole bootloader document; this pass needs only its clear colour.
fn background() -> [f32; 4] {
    let sheet = std::env::var_os("MAKEPAD_WIDGET_STYLE_FILE").and_then(|p| std::fs::read(p).ok())
        .and_then(|b| relax_compiler::json::parse(&b).ok())
        .and_then(|j| j.get("makepad_style")?.get("theme").map(|t| t.str().to_string()))
        .or_else(|| {
            let name = std::env::var("MAKEPAD_WIDGET_STYLE").ok()?;
            let path = format!("{}/widgets/themes/{name}/theme.splash", relax_compiler::run::workspace_dir());
            relax_compiler::vfs::read_to_string(&path).ok()
        });
    sheet.and_then(|s| s.lines().rev().find_map(|line| {
        let hex = line.trim().strip_prefix("mod.theme.color_bg_app")?.trim_start().strip_prefix('=')?.split("//").next()?.trim().strip_prefix('#')?;
        let hex = hex.strip_prefix('x').unwrap_or(hex);
        let n = u32::from_str_radix(hex, 16).ok()?;
        let rgba = match hex.len() { 6 => (n << 8) | 255, 8 => n, _ => return None };
        Some([((rgba >> 24) & 255) as f32 / 255.0, ((rgba >> 16) & 255) as f32 / 255.0, ((rgba >> 8) & 255) as f32 / 255.0, (rgba & 255) as f32 / 255.0])
    })).unwrap_or([0.3, 0.3, 0.3, 1.0])
}
