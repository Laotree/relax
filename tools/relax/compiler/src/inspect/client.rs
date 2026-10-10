//! `relax inspect <pid|app|all|list> <command> [args]`: the client side of the inspect protocol.
//! Finds running apps by their discovery files (relax-inspect-<pid>.json in the temp dir), sends
//! one request line and prints the answer's JSON lines (the `end` line left out). Exit status 1 when
//! the answer had an error, 2 for usage / no such app.
//!
//! `all`: every running app, including ones started later: `watch` returns the first event of any
//! of them; `events follow=1` streams all of them; other commands run on each in turn.

use std::io::{BufRead, BufReader, Write};

pub struct App {
    pub pid: u32,
    pub app: String,
    pub socket: String,
}

fn alive(pid: u32) -> bool {
    #[cfg(unix)]
    {
        extern "C" {
            fn kill(pid: i32, sig: i32) -> i32;
        }
        unsafe { kill(pid as i32, 0) == 0 }
    }
    #[cfg(not(unix))]
    {
        let _ = pid;
        false
    }
}

/// The running apps (stale discovery files of ended processes are removed).
pub fn apps() -> Vec<App> {
    let mut out = Vec::new();
    let Ok(dir) = std::fs::read_dir(std::env::temp_dir()) else { return out };
    for e in dir.flatten() {
        let name = e.file_name().to_string_lossy().into_owned();
        let Some(pid) = name.strip_prefix("relax-inspect-").and_then(|r| r.strip_suffix(".json")).and_then(|p| p.parse::<u32>().ok()) else { continue };
        if !alive(pid) {
            let _ = std::fs::remove_file(e.path());
            let _ = std::fs::remove_file(super::paths(pid).0);
            continue;
        }
        let Ok(text) = std::fs::read(e.path()) else { continue };
        let Ok(j) = crate::json::parse(&text) else { continue };
        out.push(App { pid, app: j.get("app").map(|v| v.str().to_string()).unwrap_or_default(), socket: j.get("socket").map(|v| v.str().to_string()).unwrap_or_default() });
    }
    out.sort_by_key(|a| a.pid);
    out
}

fn usage() -> i32 {
    eprintln!("usage: relax inspect <pid|app|all|list> <command> [args]   (relax inspect <pid> help: the commands)");
    2
}

pub fn main(args: &[String]) -> i32 {
    let Some(target) = args.first() else { return usage() };
    if target == "list" {
        for a in apps() {
            println!("{{\"pid\":{},\"app\":{},\"socket\":{}}}", a.pid, super::json_str(&a.app), super::json_str(&a.socket));
        }
        return 0;
    }
    if target == "schema" {
        println!("{}", super::schema());
        return 0;
    }
    let line = if args.len() > 1 { args[1..].join(" ") } else { "help".to_string() };
    let cmd = line.split_whitespace().next().unwrap_or("").to_string();
    if target == "all" {
        return all(&line, &cmd);
    }
    let list = apps();
    let chosen: Vec<&App> = match target.parse::<u32>() {
        Ok(pid) => list.iter().filter(|a| a.pid == pid).collect(),
        Err(_) => list.iter().filter(|a| &a.app == target).collect(),
    };
    let app = match chosen.as_slice() {
        [] => {
            eprintln!("relax inspect: no running app `{}` (running: {})", target, list.iter().map(|a| format!("{} {}", a.pid, a.app)).collect::<Vec<_>>().join(", "));
            return 2;
        }
        // the most recent of several with that name
        many => many[many.len() - 1],
    };
    match ask(app, &line, &mut |l| {
        println!("{}", l);
        true
    }) {
        Ok(had_err) => {
            if had_err {
                1
            } else {
                0
            }
        }
        Err(e) => {
            eprintln!("relax inspect: {} (pid {}): {}", app.app, app.pid, e);
            2
        }
    }
}

/// Sends one request; `each` gets every answer line but the end line (false: stop reading).
/// Ok(true) when the answer had an error line.
fn ask(app: &App, line: &str, each: &mut dyn FnMut(&str) -> bool) -> std::io::Result<bool> {
    #[cfg(unix)]
    {
        let mut s = std::os::unix::net::UnixStream::connect(&app.socket)?;
        s.write_all(line.as_bytes())?;
        s.write_all(b"\n")?;
        let mut err = false;
        for l in BufReader::new(s).lines() {
            let l = l?;
            if l.starts_with("{\"end\":") {
                break;
            }
            err |= l.starts_with("{\"err\":");
            if !each(&l) {
                break;
            }
        }
        Ok(err)
    }
    #[cfg(not(unix))]
    {
        let _ = (app, line, each);
        Err(std::io::Error::new(std::io::ErrorKind::Unsupported, "not available on this platform"))
    }
}

/// `all`: every app now and every app that starts while this runs.
fn all(line: &str, cmd: &str) -> i32 {
    let streaming = cmd == "watch" || (cmd == "events" && line.contains("follow=1"));
    if !streaming {
        let mut code = 0;
        for a in apps() {
            println!("{{\"app\":{},\"pid\":{}}}", super::json_str(&a.app), a.pid);
            match ask(&a, line, &mut |l| {
                println!("{}", l);
                true
            }) {
                Ok(true) => code = 1,
                Ok(false) => {}
                Err(e) => println!("{{\"err\":{}}}", super::json_str(&e.to_string())),
            }
        }
        return code;
    }
    // one reader thread per app; `watch` ends at the first event line of any
    let (tx, rx) = std::sync::mpsc::channel::<String>();
    let mut seen: Vec<u32> = Vec::new();
    let once = cmd == "watch";
    loop {
        for a in apps() {
            if seen.contains(&a.pid) {
                continue;
            }
            seen.push(a.pid);
            let tx = tx.clone();
            let line = line.to_string();
            std::thread::spawn(move || {
                let _ = ask(&a, &line, &mut |l| {
                    // only events (watch answers are events; follow streams start with a header)
                    if l.starts_with("{\"event\":") {
                        return tx.send(l.to_string()).is_ok();
                    }
                    true
                });
            });
        }
        match rx.recv_timeout(std::time::Duration::from_secs(1)) {
            Ok(l) => {
                if once && l.starts_with("{\"event\":\"none\"") {
                    continue;
                }
                println!("{}", l);
                let _ = std::io::stdout().flush();
                if once {
                    return 0;
                }
            }
            Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {}
            Err(_) => return 0,
        }
    }
}
