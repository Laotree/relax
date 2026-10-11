//! Finding running endpoints by their discovery files (`makepad-remote-<pid>.json` in the temp
//! dir). Files of processes that ended are removed when listed.

use crate::carrier::unix::paths;

#[derive(Debug, Clone)]
pub struct App {
    pub pid: u32,
    pub app: String,
    pub socket: String,
    pub started_ms: u64,
    pub caps: Vec<String>,
    /// every top-level field as (key, raw JSON value), the host's extra fields included
    pub fields: Vec<(String, String)>,
}

impl App {
    /// A string field (the host's extras such as `session_log`), unescaped.
    pub fn text(&self, key: &str) -> Option<String> {
        let raw = &self.fields.iter().find(|f| f.0 == key)?.1;
        let mut i = 0;
        string(raw.as_bytes(), &mut i)
    }

    /// Whether the endpoint serves `service` (any version).
    pub fn serves(&self, service: &str) -> bool {
        self.caps.iter().any(|c| c.split('/').next() == Some(service))
    }
}

pub(crate) fn alive(pid: u32) -> bool {
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

pub(crate) fn string(b: &[u8], i: &mut usize) -> Option<String> {
    if b.get(*i) != Some(&b'"') {
        return None;
    }
    *i += 1;
    let mut out: Vec<u8> = Vec::new();
    while *i < b.len() {
        match b[*i] {
            b'"' => {
                *i += 1;
                return String::from_utf8(out).ok();
            }
            b'\\' => {
                *i += 1;
                match *b.get(*i)? {
                    b'n' => out.push(b'\n'),
                    b't' => out.push(b'\t'),
                    b'r' => out.push(b'\r'),
                    b'u' => {
                        let h = std::str::from_utf8(b.get(*i + 1..*i + 5)?).ok()?;
                        let c = char::from_u32(u32::from_str_radix(h, 16).ok()?).unwrap_or('\u{fffd}');
                        out.extend_from_slice(c.to_string().as_bytes());
                        *i += 4;
                    }
                    c => out.push(c),
                }
                *i += 1;
            }
            c => {
                out.push(c);
                *i += 1;
            }
        }
    }
    None
}

/// The top-level `"key": value` pairs of one JSON object (values kept as raw text).
pub(crate) fn fields(text: &str) -> Vec<(String, String)> {
    let b = text.as_bytes();
    let mut i = 0;
    let mut out = Vec::new();
    while i < b.len() && b[i] != b'{' {
        i += 1;
    }
    i += 1;
    loop {
        while i < b.len() && (b[i].is_ascii_whitespace() || b[i] == b',') {
            i += 1;
        }
        if i >= b.len() || b[i] == b'}' {
            return out;
        }
        let Some(key) = string(b, &mut i) else { return out };
        while i < b.len() && (b[i].is_ascii_whitespace() || b[i] == b':') {
            i += 1;
        }
        let start = i;
        let mut depth = 0i32;
        while i < b.len() {
            match b[i] {
                b'"' => {
                    if string(b, &mut i).is_none() {
                        return out;
                    }
                    continue;
                }
                b'[' | b'{' => depth += 1,
                b']' | b'}' if depth == 0 => break,
                b']' | b'}' => depth -= 1,
                b',' if depth == 0 => break,
                _ => {}
            }
            i += 1;
        }
        out.push((key, text[start..i].trim().to_string()));
    }
}

fn list_of_strings(raw: &str) -> Vec<String> {
    let b = raw.as_bytes();
    let mut i = 0;
    let mut out = Vec::new();
    while i < b.len() {
        if b[i] == b'"' {
            match string(b, &mut i) {
                Some(s) => out.push(s),
                None => break,
            }
        } else {
            i += 1;
        }
    }
    out
}

pub fn parse(text: &str) -> Option<App> {
    let fields = fields(text);
    let get = |k: &str| fields.iter().find(|f| f.0 == k).map(|f| f.1.clone());
    let text_of = |k: &str| get(k).and_then(|r| string(r.as_bytes(), &mut 0)).unwrap_or_default();
    Some(App {
        pid: get("pid")?.parse().ok()?,
        app: text_of("app"),
        socket: text_of("socket"),
        started_ms: get("started_ms").and_then(|v| v.parse().ok()).unwrap_or(0),
        caps: get("caps").map(|r| list_of_strings(&r)).unwrap_or_default(),
        fields,
    })
}

/// The running endpoints, oldest first by pid (stale discovery files of ended processes are
/// removed).
pub fn apps() -> Vec<App> {
    let mut out = Vec::new();
    let Ok(dir) = std::fs::read_dir(std::env::temp_dir()) else { return out };
    for e in dir.flatten() {
        let name = e.file_name().to_string_lossy().into_owned();
        let Some(pid) = name.strip_prefix("makepad-remote-").and_then(|r| r.strip_suffix(".json")).and_then(|p| p.parse::<u32>().ok()) else { continue };
        if !alive(pid) {
            let _ = std::fs::remove_file(e.path());
            let _ = std::fs::remove_file(paths(pid).0);
            continue;
        }
        let Ok(text) = std::fs::read_to_string(e.path()) else { continue };
        if let Some(app) = parse(&text) {
            out.push(app);
        }
    }
    out.sort_by_key(|a| a.pid);
    out
}

/// `spec` is a pid or an app name; of several with that name the most recent (highest pid).
pub fn find(spec: &str) -> Option<App> {
    let list = apps();
    match spec.parse::<u32>() {
        Ok(pid) => list.into_iter().find(|a| a.pid == pid),
        Err(_) => list.into_iter().rfind(|a| a.app == spec),
    }
}
