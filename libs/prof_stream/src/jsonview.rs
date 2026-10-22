//! Any `makepad inspect` answer (JSON lines) as a compact answer (profproto.md §5): the `measured`
//! line or the first line becomes the finding, runs of lines with the same keys become one table
//! (header once, `_ms` / `_kb` suffixes as units in the header, numbers at 2-3 significant
//! digits), nested values are written inline, long strings are cut with the cut said, `more`
//! lists become drill-downs, and ids (P<n> panic, K<n> breakpoint) link to their locals.

use crate::ask::Ans;
use crate::text::{sig, Table};
use makepad_strict_json::Value;

/// Cells longer than this are cut.
const CELL: usize = 90;

fn scalar(v: &Value) -> String {
    match v {
        Value::Null => "-".into(),
        Value::Bool(b) => if *b { "yes".into() } else { "no".into() },
        Value::Int(i) => i.to_string(),
        Value::F64(f) => sig(*f),
        Value::Str(s) => s.clone(),
        Value::Arr(a) => a.iter().map(scalar).collect::<Vec<_>>().join(", "),
        Value::Obj(o) => o.iter().map(|(k, v)| format!("{k}={}", scalar(v))).collect::<Vec<_>>().join(" "),
    }
}

fn cut(s: String) -> String {
    if s.chars().count() <= CELL {
        return s;
    }
    let mut c: String = s.chars().take(CELL - 1).collect();
    c.push('…');
    c
}

/// A header from a key: `frame_ms` -> `frame ms`.
fn head(k: &str) -> String {
    k.replace('_', " ")
}

/// The query an id cell leads to (read-only queries only).
fn link_of(v: &str) -> Option<String> {
    let num = |p: char| v.strip_prefix(p).filter(|r| !r.is_empty() && r.chars().all(|c| c.is_ascii_digit())).is_some();
    if num('P') {
        Some(format!("locals panic={v}"))
    } else if num('K') {
        Some(format!("locals break={v}"))
    } else {
        None
    }
}

/// `cmd`'s answer lines as a compact answer.
pub fn render(cmd: &str, lines: &[String]) -> Ans {
    let mut ans = Ans::default();
    let mut rows: Vec<Vec<(String, Value)>> = Vec::new();
    let mut plain: Vec<String> = Vec::new();
    for l in lines {
        match makepad_strict_json::parse_depth(l.as_bytes(), 32) {
            Ok(Value::Obj(o)) => {
                if let Some((_, Value::Str(m))) = o.iter().find(|x| x.0 == "measured") {
                    if ans.finding.is_empty() {
                        ans.finding = m.clone();
                    }
                    continue;
                }
                if let Some((_, e)) = o.iter().find(|x| x.0 == "err") {
                    ans.finding = format!("{cmd}: {}", scalar(e));
                    continue;
                }
                rows.push(o);
            }
            _ => plain.push(l.clone()),
        }
    }
    // runs of rows with the same keys: one table each; a single-row run reads as `key: value` lines
    let mut i = 0;
    while i < rows.len() {
        let keys: Vec<String> = rows[i].iter().map(|x| x.0.clone()).filter(|k| k != "more").collect();
        let mut j = i + 1;
        while j < rows.len() && rows[j].iter().map(|x| x.0.clone()).filter(|k| k != "more").collect::<Vec<_>>() == keys {
            j += 1;
        }
        for r in &rows[i..j] {
            if let Some((_, m)) = r.iter().find(|x| x.0 == "more") {
                match m {
                    Value::Arr(a) => a.iter().for_each(|q| ans.more(scalar(q))),
                    v => ans.more(scalar(v)),
                }
            }
        }
        if j - i == 1 {
            for (k, v) in rows[i].iter().filter(|x| x.0 != "more") {
                ans.note(cut(format!("{}: {}", head(k), scalar(v))));
            }
        } else {
            let mut t = Table::new(&keys.iter().map(|k| head(k)).collect::<Vec<_>>().iter().map(String::as_str).collect::<Vec<_>>());
            for r in &rows[i..j] {
                let cells: Vec<String> = keys.iter().map(|k| r.iter().find(|x| &x.0 == k).map_or("-".to_string(), |x| cut(scalar(&x.1)))).collect();
                let link = cells.iter().find_map(|c| link_of(c));
                t.row_link(cells, link);
            }
            ans.table(t);
        }
        i = j;
    }
    for p in plain {
        ans.note(cut(p));
    }
    if ans.finding.is_empty() {
        ans.finding = match (rows.len(), lines.len()) {
            (0, 0) => format!("{cmd}: nothing"),
            (n, _) => format!("{cmd}: {n} row(s)"),
        };
    }
    ans
}
