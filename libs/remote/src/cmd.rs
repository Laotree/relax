//! The `cmd` service: the inspect line protocol of `relax inspect` and native apps. One request per
//! DATA message (a message may hold several lines); the answer is JSON lines sent as DATA, ending
//! with an `end` line. The host plugs in `dispatch`. Several cmd channels run at once, one thread
//! each. `Req`, `Out`, `answer` and the size limit are the inspect protocol's own, unchanged.

use crate::conn::{ChannelTx, Event, CLOSE_NORMAL};
use crate::endpoint::Factory;
use std::io::Write;
use std::sync::Arc;

static START: std::sync::OnceLock<std::time::Instant> = std::sync::OnceLock::new();

pub(crate) fn wall_ms() -> u64 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_millis() as u64)
}

/// ms since the first use of this crate in the process (the clock every reply uses)
pub fn now_ms() -> u64 {
    START.get_or_init(std::time::Instant::now).elapsed().as_millis() as u64
}

/// Answers one request line in memory: the reply's JSON lines (no `end` line) and whether it was
/// cut at the size limit. For hosts that call a program's commands directly (`relax inspect`).
pub fn answer(dispatch: fn(&Req, &mut Out), line: &str) -> (Vec<u8>, bool) {
    let req = Req::parse(line);
    let mut buf: Vec<u8> = Vec::new();
    let mut out = Out { w: &mut buf, bytes: 0, limit: if req.get("full") == Some("1") { usize::MAX } else { LIMIT }, truncated: false, ok: true };
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| dispatch(&req, &mut out)));
    if r.is_err() {
        out.err("internal error in this command (inspect bug)");
    }
    let truncated = out.truncated;
    (buf, truncated)
}


/// A reply being written: JSON lines, bounded (a reply never grows past `LIMIT` bytes unless the
/// request said `full=1`).
pub struct Out<'a> {
    w: &'a mut dyn Write,
    bytes: usize,
    pub limit: usize,
    pub truncated: bool,
    ok: bool,
}

const LIMIT: usize = 16 << 10;

impl<'a> Out<'a> {
    pub fn line(&mut self, s: &str) {
        if self.bytes + s.len() > self.limit {
            self.truncated = true;
            return;
        }
        self.bytes += s.len() + 1;
        self.ok &= self.w.write_all(s.as_bytes()).is_ok() && self.w.write_all(b"\n").is_ok();
    }
    /// A line that is always written (headers, errors, the end line).
    pub fn always(&mut self, s: &str) {
        self.ok &= self.w.write_all(s.as_bytes()).is_ok() && self.w.write_all(b"\n").is_ok();
    }
    pub fn err(&mut self, msg: &str) {
        self.always(&format!("{{\"err\":{}}}", json_str(msg)));
    }
    pub fn flush(&mut self) -> bool {
        self.ok &= self.w.flush().is_ok();
        self.ok
    }
    /// The measurement header every reply starts with.
    pub fn measured(&mut self, what: &str, source: &str, partial: &[String]) {
        let p: Vec<String> = partial.iter().map(|s| json_str(s)).collect();
        self.always(&format!("{{\"measured\":{},\"at_ms\":{},\"source\":{},\"partial\":[{}]}}", json_str(what), now_ms(), json_str(source), p.join(",")));
    }
}

/// A parsed request: the command word, positional words and k=v arguments.
pub struct Req {
    pub cmd: String,
    pub pos: Vec<String>,
    pub kv: Vec<(String, String)>,
}

impl Req {
    /// `cmd word k=v ...`, or one flat JSON object `{"cmd":"..","k":"v","n":1}`.
    pub fn parse(line: &str) -> Req {
        let line = line.trim();
        if line.starts_with('{') {
            if let Some(r) = parse_json_request(line) {
                return r;
            }
        }
        let mut words = line.split_whitespace();
        let cmd = words.next().unwrap_or("").to_string();
        let mut r = Req { cmd, pos: Vec::new(), kv: Vec::new() };
        for w in words {
            let w = w.trim_start_matches("--");
            match w.split_once('=') {
                Some((k, v)) => r.kv.push((k.to_string(), v.to_string())),
                None => r.pos.push(w.to_string()),
            }
        }
        r
    }
    pub fn get(&self, k: &str) -> Option<&str> {
        self.kv.iter().rev().find(|x| x.0 == k).map(|x| x.1.as_str())
    }
    pub fn num(&self, k: &str, d: u64) -> u64 {
        self.get(k).and_then(|v| v.parse().ok()).unwrap_or(d)
    }
}

/// A flat object of string / number / bool values (other values are skipped).
fn parse_json_request(s: &str) -> Option<Req> {
    let b = s.as_bytes();
    let mut i = 1;
    let mut r = Req { cmd: String::new(), pos: Vec::new(), kv: Vec::new() };
    fn ws(b: &[u8], i: &mut usize) {
        while *i < b.len() && b[*i].is_ascii_whitespace() {
            *i += 1;
        }
    }
    fn string(b: &[u8], i: &mut usize) -> Option<String> {
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
    loop {
        ws(b, &mut i);
        match b.get(i)? {
            b'}' => return Some(r),
            b',' => {
                i += 1;
                continue;
            }
            _ => {}
        }
        let key = string(b, &mut i)?;
        ws(b, &mut i);
        if b.get(i)? != &b':' {
            return None;
        }
        i += 1;
        ws(b, &mut i);
        let val = if b.get(i)? == &b'"' {
            string(b, &mut i)?
        } else {
            let st = i;
            while i < b.len() && !matches!(b[i], b',' | b'}') {
                i += 1;
            }
            let t = s[st..i].trim();
            match t {
                "true" => "1".into(),
                "false" => "0".into(),
                t if t.parse::<f64>().is_ok() => t.to_string(),
                _ => continue,
            }
        };
        if key == "cmd" {
            r.cmd = val;
        } else {
            r.kv.push((key, val));
        }
    }
}

pub fn json_str(s: &str) -> String {
    let mut o = String::with_capacity(s.len() + 2);
    o.push('"');
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            '\r' => o.push_str("\\r"),
            '\t' => o.push_str("\\t"),
            c if (c as u32) < 0x20 => o.push_str(&format!("\\u{:04x}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

/// A writer that buffers and sends the buffer as one DATA message on flush (or past 64 KiB).
/// It waits for queue room, so a slow client slows only this command thread.
struct ChanWriter {
    tx: ChannelTx,
    buf: Vec<u8>,
}

impl Write for ChanWriter {
    fn write(&mut self, b: &[u8]) -> std::io::Result<usize> {
        self.buf.extend_from_slice(b);
        if self.buf.len() >= 64 << 10 {
            self.flush()?;
        }
        Ok(b.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        if self.buf.is_empty() {
            return Ok(());
        }
        self.tx.send(std::mem::take(&mut self.buf))
    }
}

/// The `cmd` service served by `dispatch`.
pub fn service(dispatch: fn(&Req, &mut Out)) -> Factory {
    Arc::new(move |conn, open| {
        let hooks = conn.hooks();
        std::thread::Builder::new()
            .name("makepad-remote-cmd".into())
            .spawn(move || {
                (hooks.enter)();
                serve(open.channel, dispatch);
                (hooks.exit)();
            })
            .map(|_| ())
            .map_err(|e| (crate::conn::CLOSE_REFUSED, format!("cannot start the command thread: {e}")))
    })
}

fn serve(ch: crate::conn::Channel, dispatch: fn(&Req, &mut Out)) {
    let mut w = ChanWriter { tx: ch.tx(), buf: Vec::new() };
    while let Some(ev) = ch.recv() {
        let data = match ev {
            Event::Data(d) => d,
            Event::Closed(..) => break,
            Event::Opened(_) => continue,
        };
        for line in String::from_utf8_lossy(&data).lines() {
            if line.trim().is_empty() {
                continue;
            }
            let req = Req::parse(line);
            let t = std::time::Instant::now();
            let mut out = Out { w: &mut w, bytes: 0, limit: if req.get("full") == Some("1") { usize::MAX } else { LIMIT }, truncated: false, ok: true };
            let cmd = req.cmd.clone();
            // a panic in a command (a bug in the host) answers as an error, the session goes on
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| dispatch(&req, &mut out)));
            if r.is_err() {
                out.err("internal error in this command (inspect bug)");
            }
            let trunc = out.truncated;
            out.always(&format!("{{\"end\":{},\"ms\":{}{}}}", json_str(&cmd), t.elapsed().as_millis(), if trunc { ",\"truncated\":true" } else { "" }));
            if !out.flush() {
                ch.close(CLOSE_NORMAL, "");
                return;
            }
        }
    }
}
