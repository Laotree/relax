//! Optimisation remarks: what the O3 tier decided about a fn and why, recorded at every O3 build
//! (cheap: the inliner's own refusals, kept as fixed-size records) and queryable afterwards
//! (`remarks <fn>`, and `asm` names the reason next to each call it kept). Keyed by slot; a slot's
//! next O3 build replaces its remarks.

use super::{json_str, short, Out, Req};
use relax_codegen::opt::SiteRemark;
use std::collections::HashMap;

static INLINE: relax_session::sync::Mutex<Option<HashMap<u32, Vec<SiteRemark>>>> = relax_session::sync::Mutex::new(None);

/// The O3 build of slot `id` kept these call sites as calls (its last inlining round).
pub fn record_inline(id: u32, v: Vec<SiteRemark>) {
    let _k = crate::zone_alloc::kept();
    let mut g = INLINE.lock().unwrap_or_else(|e| e.into_inner());
    let m = g.get_or_insert_with(HashMap::new);
    let mut v = v;
    v.shrink_to_fit();
    m.insert(id, v);
}

/// The kept call sites of slot `id`'s last O3 build.
pub fn inline_of(id: u32) -> Vec<SiteRemark> {
    INLINE.lock().unwrap_or_else(|e| e.into_inner()).as_ref().and_then(|m| m.get(&id).cloned()).unwrap_or_default()
}

pub(crate) fn scan_kept(a: &mut crate::jit::zone_scan::Acc) {
    if let Ok(g) = INLINE.try_lock() {
        if let Some(m) = g.as_ref() {
            a.field("inspect.remarks");
            for v in m.values() {
                a.vec(v);
            }
        }
    }
}

/// `remarks <fn|@slot> [n=20]`: the O3 decisions of the fn's slots: the calls the inliner kept
/// (hot sites first) with the refusal and its numbers, the tier history of its code.
pub fn cmd_remarks(req: &Req, out: &mut Out) {
    let Some(q) = req.pos.first().cloned() else {
        return out.err("usage: remarks <fn|@slot> [n=20]");
    };
    let n = req.num("n", 20) as usize;
    let up = crate::jit::current_unit();
    if up.is_null() {
        return out.err("no running unit");
    }
    let r = crate::owner::call_within(crate::owner::Class::Job, 10_000, move || -> Result<Vec<String>, String> {
        let u = unsafe { &*up };
        let ids: Vec<u32> = match q.strip_prefix('@').and_then(|s| s.parse::<u32>().ok()) {
            Some(id) if (id as usize) < u.fns.len() => vec![id],
            _ => super::instrument::find_all(u, &q, 8).into_iter().map(|x| x.0).collect(),
        };
        if ids.is_empty() {
            return Err(format!("no fn matches `{}`; try: asm top", q));
        }
        let mut rows = Vec::new();
        for id in ids {
            let f = &u.fns[id as usize];
            let mut v = inline_of(id);
            let tiers: Vec<String> = super::codever::bodies(u, id).iter().map(|b| format!("{} ({})", super::codever::label(super::codever::kind_at(u, b.start)), b.state)).collect();
            if v.is_empty() {
                rows.push(format!("`{}` (@{}): no O3 remarks (no O3 build in this run{}); code: {}", short(&f.name, 100), id, if tiers.is_empty() { "" } else { ", or every call was inlined" }, if tiers.is_empty() { "none".into() } else { tiers.join(", ") }));
                continue;
            }
            v.sort_by_key(|r| (!r.hot, r.pos));
            let hot = v.iter().filter(|r| r.hot).count();
            rows.push(format!("`{}` (@{}): its last O3 build kept {} call(s) ({} in hot blocks); code: {}", short(&super::display_name(u, id, 0), 100), id, v.len(), hot, tiers.join(", ")));
            rows.push(String::new());
            rows.push("| line | callee | hot | why it stayed a call |".into());
            rows.push("|---|---|---|---|".into());
            for r in v.iter().take(n) {
                let at = super::codever::pos_line(u, r.pos).map(|(fi, l)| format!("{}:{}", u.prog.file_paths.get(fi as usize).map(|p| p.rsplit('/').next().unwrap_or(p)).unwrap_or("?"), l)).unwrap_or_else(|| "?".into());
                let callee = if (r.callee as usize) < u.fns.len() { super::display_name(u, r.callee, 0) } else { format!("fn#{}", r.callee) };
                rows.push(format!("| {} | `{}` | {} | {} |", at, short(&callee.replace('|', "/"), 80), if r.hot { "yes" } else { "" }, r.describe()));
            }
            if v.len() > n {
                rows.push(format!("+{} more (n=)", v.len() - n));
            }
        }
        Ok(rows)
    });
    match r.unwrap_or_else(|| Err(format!("the owner did not answer in 10 s ({})", crate::owner::serving_note()))) {
        Ok(rows) => {
            for l in rows {
                out.line(&l);
            }
            out.always("more: asm <fn> vs=rustc  versions <fn>  tier <fn> o3 fresh=1");
        }
        Err(e) => out.err(&e),
    }
    let _ = json_str;
}
