//! The HAL's domain host (HAL.md 5d): what starts, stops and relaunches apps when a privileged
//! domain (the window manager) sends `DomainStart` / `DomainStop` / `DomainRelaunch`. The HAL
//! hands each command to [`Host`]; an app starts as a domain of the running program
//! (`relax_compiler::domain::start_in_run`) with its whole run inside the launch the HAL made
//! (`makepad_hal::with_launch`: its `hal_open` opens the session the parent asked for). The
//! domain's progress, crash and exit go back to the HAL through [`observe`] as
//! `Hal::report_domain`, which tells the parent.
//!
//! The primary app of `relax run` follows the same path as children of a window manager.
//! Privilege is granted by the host (`--privileged`); JIT code cannot claim it.

use makepad_hal::{domain_state, domain_stop, with_caps, with_launch, Caps, DomainHost, DomainLaunch, Hal};
use relax_compiler::domain::{self, AppSpec, Around, DomainState};
use std::sync::Arc;
use std::time::Duration;

/// The compile phases `domain::start` reports, in order (the HAL's `phase` is the index).
const PHASES: [&str; 8] = ["package graph", "resolve", "build scripts", "loading crates", "load", "collect", "link", "main"];

#[derive(Default)]
pub struct Host;

impl Host {
    fn launch(&self, launch: DomainLaunch) -> Result<(), String> {
        let domain = launch.domain;
        let hook = launch.clone();
        let primary = crate::hal_run::spec(domain);
        let privileged = primary.is_some() && crate::PRIVILEGED.load(std::sync::atomic::Ordering::Relaxed);
        let around: Around = Arc::new(move |run: &mut dyn FnMut()| with_caps(Caps { privileged }, || with_launch(&hook, || run())));
        let mut spec = primary.unwrap_or_else(|| AppSpec {
            package: launch.app.clone(), args: launch.args.split_whitespace().map(str::to_string).collect(), ..Default::default()
        });
        spec.parent = (launch.parent != 0).then_some(launch.parent);
        spec.id = Some(domain);
        spec.around = Some(around);
        domain::prepare(&spec).map_err(|e| e.join(" | "))?;
        // The registry exists before returning to HAL, so stop can cancel the loader even
        // before it is scheduled. Never join the compiling thread ahead of cancellation.
        if let Err(e) = std::thread::Builder::new().name(format!("domain-load-{domain}")).spawn(move || {
            if let Err(e) = domain::start_prepared_in_run(spec, domain) {
                if !matches!(domain::state(domain), Some(DomainState::Stopped)) {
                    eprintln!("relax-domain: {}: {}", launch.app, e.join(" | "));
                }
            }
        }) {
            domain::loading_failed(domain, &e.to_string());
            return Err(format!("starting the loader thread: {e}"));
        }
        Ok(())
    }
}

impl DomainHost for Host {
    fn start(&self, launch: DomainLaunch) -> Result<(), String> {
        self.launch(launch)
    }

    fn stop(&self, domain: u32, mode: u32) {
        domain::begin_stop(domain);
        relax_compiler::reload::domain_stopping(domain);
        relax_compiler::inspect::stop_domain(domain);
        relax_compiler::inspect::events::release_domain(domain);
        let how = if mode == domain_stop::KILL { domain::Stop::Kill } else { domain::Stop::Quit };
        if let Err(e) = domain::stop(domain, how) { eprintln!("relax-domain: {domain}: {e}"); }
        report_stop(domain);
    }

    // The HAL stopped the old run (`stop(QUIT)` returned) and freed its session: start again.
    fn relaunch(&self, launch: DomainLaunch) -> Result<(), String> {
        let id = launch.domain;
        crate::hal_run::restarting(id);
        let result = self.launch(launch);
        if let Err(e) = &result {
            eprintln!("relax-domain: {id}: {e}");
            crate::hal_run::observe(id, &DomainState::Crashed(e.clone()));
        }
        result
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

/// `RELAX_DOMAIN_REPORT=1`: what a stop left of the domain on stderr: its state, threads, arena and
/// static-block bytes still held, the bytes teardown has freed in all so far, and the process memory.
fn report_stop(id: domain::DomainId) {
    if std::env::var_os("RELAX_DOMAIN_REPORT").is_none() {
        return;
    }
    let Some(i) = domain::info(id) else { return };
    let (rss, pss) = domain::process_memory_kb();
    eprintln!(
        "relax-domain-stop: id={id} pkg={} state={:?} threads={} arena_in_use={} arena_committed={} static_committed={} freed_by_teardown={} rss_kb={rss} pss_kb={pss}",
        i.package, i.state, i.threads, i.arena_in_use, i.arena_committed, i.static_committed, domain::freed_by_teardown()
    );
    eprintln!("relax-domain-stop-heaps: id={id} {}", domain::process_breakdown());
    // the process's memory once the stop's own work and the next frames have settled
    let _ = std::thread::Builder::new().name(format!("domain-report-{id}")).spawn(move || {
        std::thread::sleep(Duration::from_secs(8));
        let (rss, pss) = domain::process_memory_kb();
        eprintln!("relax-domain-after-stop: id={id} 8s later rss_kb={rss} pss_kb={pss}");
        eprintln!("relax-domain-after-stop-heaps: id={id} {}", domain::process_breakdown());
    });
}

/// A domain changed state (`domain::set_observer`): the HAL tells the parent.
fn observe(id: domain::DomainId, state: &DomainState) {
    let _kept = relax_compiler::zone_alloc::kept();
    crate::hal_run::observe(id, state);
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
            relax_compiler::reload::domain_stopping(id);
            hal.report_domain(id, domain_state::CRASHED, 0, 0.0, msg);
        }
        DomainState::Exited(code) => {
            relax_compiler::reload::domain_stopping(id);
            hal.report_domain(id, domain_state::EXITED, 0, 100.0, &code.to_string());
        }
        // the HAL freed the session before it asked to stop
        DomainState::Stopped => {}
        DomainState::Leaked { threads } => {
            hal.report_domain(id, domain_state::CRASHED, 0, 0.0, &format!("shutdown timed out: {threads} threads still alive; domain memory retained"));
        }
    }
}

/// Registers the host with the HAL and the observer with the domains.
pub fn register() {
    let _kept = relax_compiler::zone_alloc::kept();
    #[cfg(not(any(target_arch = "wasm32", target_os = "android", target_env = "ohos")))]
    relax_compiler::inspect::register_host_inspect("gpu", makepad_hal::inspect::dispatch);
    Hal::global().set_domain_host(Arc::new(Host::default()));
    domain::set_observer(observe);
}

pub fn start(launch: DomainLaunch) -> Result<(), String> {
    Host.launch(launch)
}
