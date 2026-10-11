//! The HAL's domain host (HAL.md 5d): what starts, stops and relaunches apps when a privileged
//! domain (the window manager) sends `DomainStart` / `DomainStop` / `DomainRelaunch`. The HAL
//! hands each command to [`Host`]; an app starts as a domain of the running program
//! (`relax_compiler::domain::start_in_run`) with its whole run inside the launch the HAL made
//! (`makepad_hal::with_launch`: its `hal_open` opens the session the parent asked for). The
//! domain's progress, crash and exit go back to the HAL through [`observe`] as
//! `Hal::report_domain`, which tells the parent.
//!
//! Domain control is these commands only. Privilege is granted here, by the host, around the
//! boot app's main (`--privileged`, [`boot_privileged`]); JIT code cannot claim it.

use makepad_hal::{domain_state, domain_stop, with_caps, with_launch, Caps, DomainHost, DomainLaunch, Hal};
use relax_compiler::domain::{self, AppSpec, Around, DomainState};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::Duration;

/// The compile phases `domain::start` reports, in order (the HAL's `phase` is the index).
const PHASES: [&str; 3] = ["package graph", "loading crates", "main"];

/// How long `stop` waits for a domain's run to end before it marks the domain stopped.
const QUIT_WAIT: Duration = Duration::from_secs(10);
const KILL_WAIT: Duration = Duration::from_secs(5);

#[derive(Default)]
pub struct Host {
    /// the threads still loading an app (compiling its crates); `stop` waits for them
    loading: Mutex<HashMap<u32, std::thread::JoinHandle<()>>>,
}

impl Host {
    fn launch(&self, launch: DomainLaunch) -> Result<(), String> {
        let domain = launch.domain;
        // loading an app takes seconds: not on the thread that sent the command (the window
        // manager's own loop)
        let handle = std::thread::Builder::new()
            .name(format!("domain-load-{domain}"))
            .spawn(move || {
                let hook = launch.clone();
                let around: Around = Arc::new(move |run: &mut dyn FnMut()| with_launch(&hook, || run()));
                let spec = AppSpec {
                    package: launch.app.clone(),
                    args: launch.args.split_whitespace().map(str::to_string).collect(),
                    parent: Some(launch.parent),
                    id: Some(domain),
                    around: Some(around),
                    ..Default::default()
                };
                if let Err(e) = domain::start_in_run(spec) {
                    let msg = e.join(" | ");
                    eprintln!("relax-domain: {}: {msg}", launch.app);
                    // (a start that failed after it began has reported its crash already)
                    if !matches!(domain::state(domain), Some(DomainState::Crashed(_))) {
                        Hal::global().report_domain(domain, domain_state::CRASHED, 0, 0.0, &msg);
                    }
                }
            })
            .map_err(|e| format!("starting the loader thread: {e}"))?;
        self.loading.lock().unwrap_or_else(|e| e.into_inner()).insert(domain, handle);
        Ok(())
    }
}

impl DomainHost for Host {
    fn start(&self, launch: DomainLaunch) -> Result<(), String> {
        self.launch(launch)
    }

    // The app was asked to quit (QUIT) or its session is freed and it hears one quit request on
    // its next pump (KILL); it ends its own run, and this returns once it did. Relax cannot park
    // or stop a thread: a domain that does not end in time is marked stopped and its thread keeps
    // running (a known gap; the HAL side is freed either way).
    fn stop(&self, domain: u32, mode: u32) {
        let loading = self.loading.lock().unwrap_or_else(|e| e.into_inner()).remove(&domain);
        if let Some(h) = loading {
            let _ = h.join();
        }
        let wait = if mode == domain_stop::KILL { KILL_WAIT } else { QUIT_WAIT };
        if !domain::wait_thread_done(domain, wait) {
            eprintln!("relax-domain: domain {domain} did not end its run within {} s: marked stopped, its thread keeps running", wait.as_secs());
            let _ = domain::stop(domain, domain::Stop::Kill);
        }
    }

    // The HAL stopped the old run (`stop(QUIT)` returned) and freed its session: start again.
    fn relaunch(&self, launch: DomainLaunch) -> Result<(), String> {
        self.launch(launch)
    }
}

/// `RELAX_DOMAIN_REPORT=1`: each domain's start is measured on stderr: the process's memory
/// (RSS/PSS kB) when the start began, at the domain's first frame and 5 s later, and the time
/// from the start to the first frame.
fn report_start(id: domain::DomainId) {
    if std::env::var_os("RELAX_DOMAIN_REPORT").is_none() {
        return;
    }
    let before = domain::process_memory_kb();
    let _ = std::thread::Builder::new().name(format!("domain-report-{id}")).spawn(move || {
        let first = domain::wait_first_frame(id, Duration::from_secs(300));
        let at = domain::process_memory_kb();
        std::thread::sleep(Duration::from_secs(5));
        let settled = domain::process_memory_kb();
        let package = domain::info(id).map(|i| i.package).unwrap_or_default();
        eprintln!(
            "relax-domain-report: id={id} pkg={package} first_frame_ms={} rss_kb={}/{}/{} pss_kb={}/{}/{}",
            first.map_or("none".to_string(), |ms| format!("{ms:.0}")),
            before.0,
            at.0,
            settled.0,
            before.1,
            at.1,
            settled.1
        );
    });
}

/// A domain changed state (`domain::set_observer`): the HAL tells the parent.
fn observe(id: domain::DomainId, state: &DomainState) {
    let hal = Hal::global();
    match state {
        DomainState::Compiling(phase) => {
            if *phase == PHASES[0] {
                report_start(id);
            }
            let at = PHASES.iter().position(|p| *p == phase.as_str()).unwrap_or(0);
            hal.report_domain(id, domain_state::COMPILING, at as u32, at as f32 * 100.0 / PHASES.len() as f32, phase);
        }
        DomainState::Running => {
            hal.report_domain(id, domain_state::RUNNING, 0, 100.0, "");
        }
        DomainState::Crashed(msg) => {
            hal.report_domain(id, domain_state::CRASHED, 0, 0.0, msg);
        }
        DomainState::Exited(code) => {
            hal.report_domain(id, domain_state::EXITED, 0, 100.0, &code.to_string());
        }
        // the HAL freed the session before it asked to stop
        DomainState::Stopped => {}
    }
}

/// Registers the host with the HAL and the observer with the domains.
pub fn register() {
    Hal::global().set_domain_host(Arc::new(Host::default()));
    domain::set_observer(observe);
}

/// `relax run --privileged`: the boot app's main runs with the capabilities of a window manager
/// (it may use the HAL's domain control commands).
pub fn boot_privileged() {
    domain::set_boot_around(Arc::new(|run: &mut dyn FnMut()| with_caps(Caps { privileged: true }, || run())));
}
