//! The relay: what runs on a remote box (`ssh <host> relax remote-relay`, or `--dial` to a hub)
//! so the hub can reach the box's endpoints. It is an [`Endpoint`] serving, over the one link:
//!
//! - `list`: the box's endpoints from its discovery files, one JSON line each;
//! - `session`: `launch [cwd=<dir>] <app> [args...]` starts the configured launcher (hidden, muted)
//!   and reports its PID, `kill <pid>` ends a process this relay launched, `launched` lists them;
//! - `fwd`: args `<pid|app> <service> [args]`: opens `service` on that local endpoint and bridges
//!   the two channels, so the hub's channel talks to the endpoint as if it were local.

use crate::cmd::json_str;
use crate::conn::{Channel, ChannelTx, Event, CLOSE_LINK_LOST, CLOSE_REFUSED};
use crate::endpoint::{Endpoint, Factory};
use crate::lines;
use crate::link::{Client, Error};
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::Relaxed};
use std::sync::{Arc, Mutex};
use std::time::Duration;

/// How the relay starts sessions.
#[derive(Clone)]
pub struct Config {
    /// the endpoint name the relay reports in its hello (the host name for a dial relay)
    pub name: String,
    /// the launcher's argv before the app, e.g. `["[path]/bin/relax", "run"]`
    pub launch: Vec<String>,
    /// environment of launched sessions (hidden windows, muted audio)
    pub env: Vec<(String, String)>,
}

struct Launched {
    pid: u32,
    app: String,
    log: PathBuf,
    exit: Arc<Mutex<Option<String>>>,
}

struct State {
    cfg: Config,
    launched: Mutex<Vec<Launched>>,
}

/// The relay endpoint.
pub fn endpoint(cfg: Config) -> Endpoint {
    let ep = Endpoint::new(&cfg.name);
    let st = Arc::new(State { cfg, launched: Mutex::new(Vec::new()) });
    ep.register("list", 1, lines::service("list", Arc::new(|_, out| list(out))));
    let s = st.clone();
    ep.register("session", 1, lines::service("session", Arc::new(move |line, out| session(&s, line, out))));
    ep.register("fwd", 1, fwd());
    ep
}

fn list(out: &mut Vec<String>) {
    for a in crate::discovery::apps() {
        let caps: Vec<String> = a.caps.iter().map(|c| json_str(c)).collect();
        out.push(format!("{{\"pid\":{},\"app\":{},\"socket\":{},\"started_ms\":{},\"caps\":[{}]}}", a.pid, json_str(&a.app), json_str(&a.socket), a.started_ms, caps.join(",")));
    }
}

fn err(out: &mut Vec<String>, msg: &str) {
    out.push(format!("{{\"err\":{}}}", json_str(msg)));
}

fn session(st: &State, line: &str, out: &mut Vec<String>) {
    let mut words = line.split_whitespace();
    match words.next() {
        Some("launch") => launch(st, words.collect(), out),
        Some("kill") => match words.next().and_then(|p| p.parse::<u32>().ok()) {
            Some(pid) => kill(st, pid, out),
            None => err(out, "usage: kill <pid>"),
        },
        Some("launched") => {
            for l in st.launched.lock().unwrap().iter() {
                let state = l.exit.lock().unwrap().clone().unwrap_or_else(|| "running".into());
                out.push(format!("{{\"pid\":{},\"app\":{},\"state\":{},\"log\":{}}}", l.pid, json_str(&l.app), json_str(&state), json_str(&l.log.display().to_string())));
            }
        }
        _ => err(out, "session: launch [cwd=<dir>] <app> [args...] | kill <pid> | launched"),
    }
}

#[cfg(unix)]
fn launch(st: &State, mut words: Vec<&str>, out: &mut Vec<String>) {
    use std::os::unix::process::CommandExt;
    use std::process::{Command, Stdio};
    let cwd = match words.first().and_then(|w| w.strip_prefix("cwd=")) {
        Some(dir) => {
            let dir = dir.to_string();
            words.remove(0);
            Some(dir)
        }
        None => None,
    };
    let Some((app, args)) = words.split_first() else { return err(out, "usage: launch [cwd=<dir>] <app> [args...]") };
    let Some((exe, prefix)) = st.cfg.launch.split_first() else { return err(out, "this relay has no launcher configured") };
    let log = std::env::temp_dir().join(format!("makepad-remote-launch-{}-{}.log", std::process::id(), crate::cmd::wall_ms()));
    let Ok(logfile) = std::fs::File::create(&log) else { return err(out, "cannot create the session log") };
    let Ok(logfile2) = logfile.try_clone() else { return err(out, "cannot create the session log") };
    let mut cmd = Command::new(exe);
    cmd.args(prefix).arg(app).args(args).stdin(Stdio::null()).stdout(logfile).stderr(logfile2).process_group(0);
    for (k, v) in &st.cfg.env {
        cmd.env(k, v);
    }
    if let Some(dir) = &cwd {
        cmd.current_dir(dir);
    }
    match cmd.spawn() {
        Ok(mut child) => {
            let pid = child.id();
            let exit = Arc::new(Mutex::new(None));
            let e2 = exit.clone();
            let _ = std::thread::Builder::new().name("makepad-remote-reap".into()).spawn(move || {
                let r = child.wait().map_or_else(|e| format!("lost: {e}"), |s| format!("exited {s}"));
                *e2.lock().unwrap() = Some(r);
            });
            st.launched.lock().unwrap().push(Launched { pid, app: app.to_string(), log: log.clone(), exit });
            out.push(format!("{{\"launched\":{pid},\"app\":{},\"log\":{}}}", json_str(app), json_str(&log.display().to_string())));
        }
        Err(e) => err(out, &format!("cannot start {exe}: {e}")),
    }
}

#[cfg(not(unix))]
fn launch(_: &State, _: Vec<&str>, out: &mut Vec<String>) {
    err(out, "session launch is not available on Windows yet");
}

#[cfg(unix)]
fn kill(st: &State, pid: u32, out: &mut Vec<String>) {
    extern "C" {
        fn kill(pid: i32, sig: i32) -> i32;
    }
    let l = st.launched.lock().unwrap();
    let Some(rec) = l.iter().find(|l| l.pid == pid) else { return err(out, &format!("pid {pid} was not launched by this relay")) };
    if rec.exit.lock().unwrap().is_some() {
        return err(out, &format!("pid {pid} has already exited"));
    }
    // the session is its own process group (its windows, helpers and threads end with it)
    if unsafe { kill(-(pid as i32), 15) } == 0 {
        // a session that ignores SIGTERM (or is stuck) is ended for good after 3 s
        let exit = rec.exit.clone();
        let _ = std::thread::Builder::new().name("makepad-remote-reap".into()).spawn(move || {
            std::thread::sleep(Duration::from_secs(3));
            if exit.lock().unwrap().is_none() {
                unsafe { kill(-(pid as i32), 9) };
            }
        });
        out.push(format!("{{\"killed\":{pid}}}"));
    } else {
        err(out, &format!("cannot signal {pid}"));
    }
}

#[cfg(not(unix))]
fn kill(_: &State, _: u32, out: &mut Vec<String>) {
    err(out, "session kill is not available on Windows yet");
}

fn fwd() -> Factory {
    Arc::new(|_, open| {
        let mut it = open.args.splitn(3, ' ');
        let (spec, service, args) = (it.next().unwrap_or(""), it.next().unwrap_or(""), it.next().unwrap_or(""));
        if spec.is_empty() || service.is_empty() || spec.contains('/') {
            return Err((CLOSE_REFUSED, format!("fwd: expected `<pid|app> <service> [args]`, got `{}`", open.args)));
        }
        let client = Client::connect(spec).map_err(|e| (CLOSE_REFUSED, e.to_string()))?;
        let up = client.open(service, args).map_err(to_close)?;
        bridge(open.channel, up, move || client.close());
        Ok(())
    })
}

fn to_close(e: Error) -> (u16, String) {
    match e {
        Error::LinkLost(w) => (CLOSE_LINK_LOST, w),
        Error::Refused(c, w) => (c, w),
        Error::Timeout => (CLOSE_REFUSED, e.to_string()),
        Error::Io(e) => (CLOSE_REFUSED, e.to_string()),
    }
}

/// Copies messages both ways between two channels until either closes; the close (with its code
/// and reason) is passed on. `finish` runs once both directions have ended.
pub fn bridge(a: Channel, b: Channel, finish: impl FnOnce() + Send + 'static) {
    let (atx, btx) = (a.tx(), b.tx());
    let dead = Arc::new(AtomicBool::new(false));
    let left = Arc::new(AtomicUsize::new(2));
    let finish: Arc<Mutex<Option<Box<dyn FnOnce() + Send>>>> = Arc::new(Mutex::new(Some(Box::new(finish))));
    for (from, to) in [(a, btx), (b, atx)] {
        let (dead, left, finish) = (dead.clone(), left.clone(), finish.clone());
        let _ = std::thread::Builder::new().name("makepad-remote-bridge".into()).spawn(move || {
            pump(&from, &to, &dead);
            dead.store(true, Relaxed);
            if left.fetch_sub(1, Relaxed) == 1 {
                if let Some(f) = finish.lock().unwrap().take() {
                    f();
                }
            }
        });
    }
}

fn pump(from: &Channel, to: &ChannelTx, dead: &AtomicBool) {
    loop {
        match from.recv_timeout(Duration::from_millis(300)) {
            Ok(Event::Data(d)) => {
                if to.send(d).is_err() {
                    return;
                }
            }
            Ok(Event::Closed(code, why)) => {
                to.close(code, &why);
                return;
            }
            Ok(Event::Opened(_)) => {}
            Err(true) => {
                if dead.load(Relaxed) {
                    return;
                }
            }
            Err(false) => {
                to.close(CLOSE_LINK_LOST, "channel gone");
                return;
            }
        }
    }
}

/// The credentials a dial relay presents: the key in `key_file`, the hub's pinned `fingerprint`
/// (hex; empty: trust on first contact, recorded in `known_hosts`).
#[cfg(not(target_arch = "wasm32"))]
pub fn credentials(key_file: &std::path::Path, fingerprint: &str, known_hosts: PathBuf) -> std::io::Result<makepad_network::tunnel::ClientCredentials> {
    use makepad_network::tunnel::{parse_key_file, ClientCredentials};
    let keys = parse_key_file(&std::fs::read_to_string(key_file)?)?;
    let expect = if fingerprint.is_empty() { None } else { Some(makepad_network::tls::from_hex::<32>(fingerprint).ok_or_else(|| std::io::Error::new(std::io::ErrorKind::InvalidInput, "the fingerprint must be 64 hex digits"))?) };
    Ok(ClientCredentials { keys, known_hosts: Some(makepad_network::tls::KnownHosts::new(known_hosts)), expect })
}

/// Serves the relay over this process's stdin/stdout until the hub is gone.
pub fn serve_stdio(ep: &Endpoint) -> std::io::Result<()> {
    crate::carrier::stdio::serve_own(ep)
}

/// Dials the hub at `addr` and serves the relay over that connection; when the link drops it
/// dials again (backoff 1 s doubling to 30 s) and sends RESUME with the same link id. Never
/// returns.
#[cfg(not(target_arch = "wasm32"))]
pub fn dial_forever(ep: &Endpoint, addr: &str, creds: &makepad_network::tunnel::ClientCredentials) -> ! {
    let link_id = format!("{}-{:x}", std::process::id(), crate::cmd::wall_ms());
    let mut backoff = 1u64;
    let mut ever = false;
    loop {
        match crate::carrier::tcp::dial(addr, creds) {
            Ok(car) => match ep.connect(car, &link_id) {
                Ok(conn) => {
                    backoff = 1;
                    if ever {
                        conn.send_control(crate::hello::encode_resume(&crate::hello::Resume { link_id: link_id.clone(), seqs: Vec::new() }));
                    }
                    ever = true;
                    eprintln!("remote-relay: linked to {addr}");
                    conn.wait_closed();
                    eprintln!("remote-relay: link to {addr} lost: {}", conn.close_reason());
                }
                Err(e) => eprintln!("remote-relay: {addr}: {e}"),
            },
            Err(e) => eprintln!("remote-relay: cannot reach {addr}: {e}"),
        }
        std::thread::sleep(Duration::from_secs(backoff));
        backoff = (backoff * 2).min(30);
    }
}
