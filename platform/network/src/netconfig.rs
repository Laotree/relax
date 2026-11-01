//! User network settings in `<MAKEPAD_HOME or ~/.makepad>/network.conf`.

use std::fs::{self, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::SystemTime;

pub const NETWORKED_AI_HUB_KEY: &str = "networked_ai_hub";

const HEADER: &str = "# Networked AI hub lets apps find and use AI hubs on the local network\n\
# and lets this machine's hub serve peers on that network.\n\
# Default: off, to avoid the macOS local-network permission prompt.\n\
# Apps read this setting when they connect. The runner's Settings toggles it.\n\
# networked_ai_hub = off|on\n\n";

struct Cached {
    path: PathBuf,
    modified: SystemTime,
    len: u64,
    on: bool,
}

static CACHE: Mutex<Option<Cached>> = Mutex::new(None);

/// Read the current setting. Missing, unreadable or invalid configuration means off.
/// Unchanged files cost one stat; no file I/O is performed while holding the cache lock.
///
/// `MAKEPAD_NETWORKED_AI_HUB=1` / `=0` overrides the file for this process (a test machine or a
/// test that needs a LAN hub sets it, as `MAKEPAD_LAN` does).
pub fn networked_ai_hub() -> bool {
    match std::env::var("MAKEPAD_NETWORKED_AI_HUB").ok().as_deref().map(str::trim) {
        Some("1") => return true,
        Some("0") => return false,
        _ => {}
    }
    let path = crate::fleet::makepad_home().join("network.conf");
    read_at(&path)
}

fn read_at(path: &Path) -> bool {
    let stamp = fs::metadata(path).and_then(|meta| Ok((meta.modified()?, meta.len())));
    let Ok((modified, len)) = stamp else {
        *CACHE.lock().unwrap_or_else(|e| e.into_inner()) = None;
        return false;
    };
    {
        let cached = CACHE.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(cached) = cached.as_ref() {
            if cached.path == path && cached.modified == modified && cached.len == len {
                return cached.on;
            }
        }
    }
    let on = fs::read_to_string(path).is_ok_and(|text| parse(&text));
    *CACHE.lock().unwrap_or_else(|e| e.into_inner()) = Some(Cached { path: path.to_path_buf(), modified, len, on });
    on
}

/// Atomically replace just this setting, preserving other keys and comments.
pub fn set_networked_ai_hub(on: bool) -> io::Result<()> {
    set_at(&crate::fleet::makepad_home().join("network.conf"), on)
}

fn set_at(path: &Path, on: bool) -> io::Result<()> {
    let home = path.parent().ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "network.conf needs a parent directory"))?;
    fs::create_dir_all(home)?;
    let text = match fs::read_to_string(path) {
        Ok(text) => text,
        Err(e) if e.kind() == io::ErrorKind::NotFound => HEADER.to_string(),
        Err(e) => return Err(e),
    };
    static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);
    let (temp, mut file) = loop {
        let id = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
        let temp = home.join(format!(".network.conf.{}.{id}.tmp", std::process::id()));
        match OpenOptions::new().write(true).create_new(true).open(&temp) {
            Ok(file) => break (temp, file),
            Err(e) if e.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(e) => return Err(e),
        }
    };
    let result = (|| {
        file.write_all(set_in(&text, on).as_bytes())?;
        file.sync_all()
    })();
    drop(file);
    let result = result.and_then(|_| fs::rename(&temp, path));
    if result.is_err() {
        let _ = fs::remove_file(&temp);
    }
    *CACHE.lock().unwrap_or_else(|e| e.into_inner()) = None;
    result
}

fn parse(text: &str) -> bool {
    text.lines().filter_map(|line| {
        let (key, value) = line.split('#').next()?.split_once('=')?;
        (key.trim() == NETWORKED_AI_HUB_KEY).then(|| value.trim() == "on")
    }).last().unwrap_or(false)
}

fn set_in(text: &str, on: bool) -> String {
    let value = if on { "on" } else { "off" };
    let mut out = String::with_capacity(text.len() + 32);
    let mut found = false;
    for line in text.split_inclusive('\n') {
        let content = line.split('#').next().unwrap_or(line);
        if let Some((key, old)) = content.split_once('=') {
            if key.trim() == NETWORKED_AI_HUB_KEY {
                found = true;
                let leading = old.len() - old.trim_start_matches([' ', '\t']).len();
                let end = old.trim_end().len().max(leading);
                out.push_str(key);
                out.push('=');
                out.push_str(&old[..leading]);
                out.push_str(value);
                out.push_str(&old[end..]);
                out.push_str(&line[content.len()..]);
                continue;
            }
        }
        out.push_str(line);
    }
    if !found {
        if !out.is_empty() && !out.ends_with('\n') {
            out.push('\n');
        }
        out.push_str(&format!("{NETWORKED_AI_HUB_KEY} = {value}\n"));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn file_round_trip_without_changing_makepad_home() {
        let unique = SystemTime::now().duration_since(SystemTime::UNIX_EPOCH).unwrap().as_nanos();
        let dir = std::env::temp_dir().join(format!("makepad-network-conf-{}-{unique}", std::process::id()));
        let path = dir.join("network.conf");
        assert!(!read_at(&path));
        set_at(&path, true).unwrap();
        assert!(fs::read_to_string(&path).unwrap().starts_with(HEADER));
        assert!(read_at(&path));
        set_at(&path, false).unwrap();
        assert!(!read_at(&path));
        fs::remove_file(&path).unwrap();
        fs::remove_dir(&dir).unwrap();
        assert!(!read_at(&path));
    }

    #[test]
    fn absent_and_garbage_are_off() {
        for text in ["", "other = on\n", "# networked_ai_hub = on\n", "networked_ai_hub = yes", "networked_ai_hub = ON", "networked_ai_hub =", "networked_ai_hub = on\nnetworked_ai_hub = garbage"] {
            assert!(!parse(text), "{text}");
        }
        assert!(parse("networked_ai_hub = on"));
        assert!(parse("  networked_ai_hub = on # enabled\n"));
    }

    #[test]
    fn setting_preserves_other_lines_and_comments() {
        let text = "# user notes\r\nother = on\r\n networked_ai_hub = off  # hub\r\n# end";
        let enabled = "# user notes\r\nother = on\r\n networked_ai_hub = on  # hub\r\n# end";
        assert_eq!(set_in(text, true), enabled);
        assert_eq!(set_in(enabled, false), text);
        assert_eq!(set_in("# notes\nother = on", false), "# notes\nother = on\nnetworked_ai_hub = off\n");
        assert_eq!(set_in("", true), "networked_ai_hub = on\n");
        assert_eq!(set_in("networked_ai_hub = on\nnetworked_ai_hub = yes\n", false), "networked_ai_hub = off\nnetworked_ai_hub = off\n");
    }
}
