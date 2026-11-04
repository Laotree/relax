#!/usr/bin/env python3
"""An edit of a const or a static reaches a program whose code came from the disk cache: its readers,
read directly or through other stored code, show the new value, or the edit asks for a restart. And
a new run of the edited sources shows the new value. "Patched" with the old value is the one wrong
answer, and a warm run with the old value the other.

usage: run.py --makepad <makepad binary> [--only p1,p2] [--cold]   (MAKEPAD_RUN_STD in the environment)

Copies pkg/ to a temporary dir with a fresh disk cache and fills it (a run, then a warm run that must
prelink). Then each probe gets a live session of its own (`makepad run` of a working tree), started
warm: one edit, and within 20 s either
  landed:   the program prints the new value, or
  restart:  the JIT offers a restart and the program keeps its old value, and `session relaunch`
            brings the new value,
and in both a fresh run of the edited sources (read-only on the cache) prints the new value.
A probe that reads late first calls its reader after the edit: that code comes from the store then.
A stored entry can be older than the manifest of the run that reads it: the edited text's first run,
reaching none of the late readers, writes its own manifest (its keys are "unchanged" from then on),
and the next run's first late reads must still see that the entries they find are of the old text.
--cold: the same sessions with the disk cache off, for comparison.
Prints a row per probe and exits 1 on any stale one.
"""
import os, re, shutil, signal, subprocess, sys, tempfile, threading, time

HERE = os.path.dirname(os.path.abspath(__file__))
args = sys.argv[1:]
relax = os.path.abspath(args[args.index("--makepad") + 1])
only = args[args.index("--only") + 1].split(",") if "--only" in args else None
cold = "--cold" in args
V = "src/values.rs"
M = "src/main.rs"
# probe -> (the printed name, file, old text, new text, the value it prints after the edit)
PROBES = [
    ("const_direct", V, "CONST_DIRECT: u64 = 1;", "CONST_DIRECT: u64 = 2;", 2),
    ("const_through", V, "CONST_THROUGH: u64 = 1;", "CONST_THROUGH: u64 = 2;", 2),
    ("const_inlined", V, "CONST_INLINED: u64 = 1;", "CONST_INLINED: u64 = 2;", 2),
    ("const_derived", V, "CONST_BASE: u64 = 1;", "CONST_BASE: u64 = 2;", 4),
    ("const_assoc", V, "for A {\n    const K: u64 = 1;", "for A {\n    const K: u64 = 2;", 2),
    ("const_assoc_named", V, "for B {\n    const K: u64 = 1;", "for B {\n    const K: u64 = 2;", 2),
    ("const_assoc_foreign", V, "for warm_const_dep::DepT {\n    const K: u64 = 1;", "for warm_const_dep::DepT {\n    const K: u64 = 2;", 2),
    ("const_assoc_dep_generic", V, "const DK: u64 = 1;", "const DK: u64 = 2;", 2),
    ("const_assoc_wrapped", V, "for Vec<W3> {\n    const K: u64 = 1;", "for Vec<W3> {\n    const K: u64 = 2;", 2),
    ("const_assoc_prim", V, "for u32 {\n    const K: u64 = 1;", "for u32 {\n    const K: u64 = 2;", 2),
    ("const_assoc_blanket", V, "const BL: u64 = 1;", "const BL: u64 = 2;", 2),
    ("const_assoc_closure", V, "for Cl {\n    const K: u64 = 1;", "for Cl {\n    const K: u64 = 2;", 2),
    ("const_assoc_chain", V, "for A4 {\n    const K: u64 = 1;", "for A4 {\n    const K: u64 = 2;", 3),
    ("const_opaque", V, "for Op {\n    const K: u64 = 1;", "for Op {\n    const K: u64 = 2;", 2),
    ("const_inferred", V, "for Inf {\n    const K: u64 = 1;", "for Inf {\n    const K: u64 = 2;", 2),
    ("trait_default", V, "const D: u64 = 1;", "const D: u64 = 2;", 2),
    ("method_default", V, "fn m() -> u64 {\n        1\n", "fn m() -> u64 {\n        2\n", 2),
    ("type_assoc", V, "for C {\n    type Out = u8;", "for C {\n    type Out = u16;", 2),
    ("type_assoc_field", V, "for C2 {\n    type Out = u8;", "for C2 {\n    type Out = u16;", 2),
    ("const_generic", V, "CONST_GEN: usize = 1;", "CONST_GEN: usize = 2;", 2),
    ("const_generic_assoc", V, "CONST_GEN_TY: usize = 1;", "CONST_GEN_TY: usize = 2;", 2),
    ("const_array_arg", V, "CONST_ARR: usize = 1;", "CONST_ARR: usize = 2;", 2),
    ("const_array_assoc", V, "for D1 {\n    const K: u64 = 1;", "for D1 {\n    const K: u64 = 2;", 2),
    ("const_array_ty", V, "CONST_ARR_TY: usize = 1;", "CONST_ARR_TY: usize = 2;", 2),
    ("impl_added", V, "// impl_added\n", "impl Drop for Plain {\n    fn drop(&mut self) {}\n}\n", 1),
    ("impl_removed", V, "impl Drop for Droppy {\n    fn drop(&mut self) {}\n}\n", "", 0),
    ("impl_added_glue", V, "// impl_added_glue\n", "impl Drop for Glue {\n    fn drop(&mut self) {\n        GLUE_DROPS.store(1, std::sync::atomic::Ordering::Relaxed);\n    }\n}\n", 1),
    # a marker impl: no call reaches it, but it picks which of std's specializing impls an instance takes
    ("impl_added_spec", V, "// impl_added_spec\n", "impl Copy for Sp {}\n", 1),
    ("const_macro", V, "CONST_MACRO: u64 = 1;", "CONST_MACRO: u64 = 2;", 2),
    ("const_macro_same", M, "CONST_MACRO_SAME: u64 = 1;", "CONST_MACRO_SAME: u64 = 2;", 2),
    ("const_pattern", V, "CONST_PATTERN: u64 = 1;", "CONST_PATTERN: u64 = 2;", 2),
    ("const_len", V, "CONST_LEN: usize = 1;", "CONST_LEN: usize = 2;", 2),
    ("const_dep", "dep/src/lib.rs", "DEP_VALUE: u64 = 1;", "DEP_VALUE: u64 = 2;", 2),
    ("const_same", V, "CONST_SAME: u64 = 1;", "CONST_SAME: u64 = 2;", 2),
    ("const_include", "src/data.txt", "x", "xx", 2),
    ("body_include", "src/body.txt", "y", "yy", 2),
    ("const_late", V, "CONST_LATE: u64 = 1;", "CONST_LATE: u64 = 2;", 2),
    ("body_inlined", V, "pub fn tiny() -> u64 {\n    1\n", "pub fn tiny() -> u64 {\n    2\n", 2),
    ("body_late", V, "pub fn late_tiny() -> u64 {\n    1\n", "pub fn late_tiny() -> u64 {\n    2\n", 2),
    ("always_late", V, "pub fn late_always() -> u64 {\n    1\n", "pub fn late_always() -> u64 {\n    2\n", 2),
    ("static_direct", V, "STATIC_DIRECT: u64 = 1;", "STATIC_DIRECT: u64 = 2;", 2),
    ("static_through", V, "STATIC_THROUGH: u64 = 1;", "STATIC_THROUGH: u64 = 2;", 2),
    ("static_late", V, "STATIC_LATE: u64 = 1;", "STATIC_LATE: u64 = 2;", 2),
]
tmp = tempfile.mkdtemp(prefix="warm-const-edit-")
pkg = os.path.join(tmp, "pkg")
shutil.copytree(os.path.join(HERE, "pkg"), pkg)
env = dict(os.environ, MAKEPAD_RUN_CACHE_DIR=os.path.join(tmp, "cache"), MAKEPAD_RUN_TARGET_DIR=os.path.join(tmp, "target"))
for k in ("MAKEPAD_RUN_CACHE", "MAKEPAD_RUN_PRELINK", "WARM_EDIT_ONCE", "WARM_EDIT_LATE"):
    env.pop(k, None)
if cold:
    env["MAKEPAD_RUN_CACHE"] = "0"
cmd = [relax, "run", "--verbose", "cache-warm-const-edit"]


def once(tag, mode, **more):
    p = subprocess.run(cmd, cwd=pkg, env=dict(env, WARM_EDIT_ONCE=mode, **more), stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=600)
    open(os.path.join(tmp, tag + ".log"), "w").write(p.stdout + p.stderr)
    return p


def value(line, probe):
    m = re.search(r"\b%s=(\d+)" % probe, line)
    return int(m.group(1)) if m else None


def save(path, text):
    # a new mtime even within the same second: write, then bump the time
    with open(path, "w") as f:
        f.write(text)
    st = os.stat(path)
    os.utime(path, ns=(st.st_atime_ns, st.st_mtime_ns + 1_000_000))


def wait(pred, secs):
    t = time.time()
    while time.time() - t < secs:
        if pred():
            return True
        time.sleep(0.02)
    return False


def session(probe, rel, old, new, want):
    path = os.path.join(pkg, rel)
    base = open(path).read()
    assert old in base, old
    ready = os.path.join(tmp, "live-ready")
    late = os.path.join(tmp, "late")
    for f in (ready, late):
        if os.path.exists(f):
            os.remove(f)
    p = subprocess.Popen(cmd, cwd=pkg, env=dict(env, MAKEPAD_RUN_LIVE_READY=ready, MAKEPAD_RUN_RELOAD_TRACE="1", WARM_EDIT_LATE=late, MAKEPAD_REMOTE="1"), stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
    out, err = [], []
    def pump(f, acc):
        for line in f:
            acc.append(line.rstrip("\n"))
    threading.Thread(target=pump, args=(p.stdout, out), daemon=True).start()
    threading.Thread(target=pump, args=(p.stderr, err), daemon=True).start()
    def last():
        return next((l for l in reversed(out) if l.startswith("out tick ")), None)
    row = {"probe": probe, "outcome": "no start", "value": None, "patch": "", "trace": ""}
    try:
        if not wait(lambda: last() is not None and os.path.exists(ready), 120):
            return row, err
        if not cold and not any("prelinked" in l for l in err) and not wait(lambda: any("prelinked" in l for l in err), 5):
            row["outcome"] = "not warm"
            return row, err
        save(path, base.replace(old, new))
        said = lambda: next((l for l in err if ": patched (" in l or "a restart applies it" in l or "REFUSED" in l), None)
        wait(lambda: said() is not None, 20)
        line = said() or ""
        restart = "a restart applies it" in line
        if not restart:
            # the late readers' first call, once the edit is in
            open(late, "w").close()
        landed = wait(lambda: last() is not None and value(last(), probe) == want, 2 if line else 0)
        row["value"] = value(last() or "", probe)
        row["patch"] = re.sub(r"^.*?: ", "", line)[:96]
        t = next((l for l in reversed(err) if l.startswith("reload-trace:")), "")
        row["trace"] = " ".join(x for x in t.split() if re.match(r"(rung|changed_consts|changed_statics|selected_slots|installed)=", x))
        if landed:
            row["outcome"] = "landed"
        elif restart:
            row["outcome"] = "restart"
            open(late, "w").close()
            subprocess.run([relax, "inspect", str(p.pid), "session", "relaunch"], env=env, capture_output=True, text=True)
            if not wait(lambda: value(last() or "", probe) == want, 60):
                row["outcome"] = "RELAUNCH STALE"
            row["relaunch"] = value(last() or "", probe)
        elif not line:
            row["outcome"] = "no answer"
        else:
            row["outcome"] = "STALE"
        return row, err
    finally:
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        p.wait()
        if row["outcome"] != "no start":
            open(late, "w").close()
            r = once("fresh-" + probe, "1", MAKEPAD_RUN_CACHE="readonly", WARM_EDIT_LATE=late) if not cold else once("fresh-" + probe, "1", WARM_EDIT_LATE=late)
            line = next((l for l in r.stdout.splitlines() if l.startswith("out tick ")), "")
            row["fresh"] = value(line, probe)
            if row["fresh"] != want:
                row["outcome"] += " + FRESH RUN STALE"
        save(path, base)


fails = 0
if not cold:
    p = once("fill", "fill")
    if p.returncode != 0:
        sys.exit("fill run failed: " + p.stderr[-2000:])
    p = once("warm", "1")
    if p.returncode != 0 or "prelinked" not in p.stderr:
        sys.exit("warm run did not prelink: " + p.stderr[-2000:])


def older_than_manifest():
    """The late readers' entries are stored by the fill; the edited text's manifest comes after them."""
    probes = [p for p in PROBES if p[0] in ("const_late", "static_late", "body_late", "always_late")]
    path = os.path.join(pkg, V)
    base = open(path).read()
    text = base
    for _, _, old, new, _ in probes:
        assert text.count(old) == 1, old
        text = text.replace(old, new)
    save(path, text)
    try:
        p = once("manifest", "many")
        if "startup manifest rewritten" not in p.stderr or "startup manifest kept" in p.stderr:
            return "the edited text's run wrote no manifest of its own"
        late = os.path.join(tmp, "late-older")
        open(late, "w").close()
        p = once("older", "1", WARM_EDIT_LATE=late)
        line = next((l for l in p.stdout.splitlines() if l.startswith("out tick ")), "")
        wrong = ["%s=%s want %d" % (n, value(line, n), w) for n, _, _, _, w in probes if value(line, n) != w]
        return ", ".join(wrong)
    finally:
        save(path, base)


if not cold and (not only or "older_than_manifest" in only):
    why = older_than_manifest()
    print("%-23s %s" % ("older_than_manifest", why or "ok"))
    fails += 1 if why else 0
for probe, rel, old, new, want in PROBES:
    if only and probe not in only:
        continue
    row, err = session(probe, rel, old, new, want)
    ok = row["outcome"] in ("landed", "restart")
    fails += 0 if ok else 1
    print("%-23s %-15s value=%-4s want=%-2s relaunch=%-4s fresh=%-4s %s | %s" % (probe, row["outcome"], row["value"], want, row.get("relaunch", "-"), row.get("fresh", "-"), row["trace"], row["patch"]), flush=True)
    if not ok and "-v" in args:
        for l in err[-12:]:
            print("    | " + l[:200])
shutil.rmtree(tmp, ignore_errors=True)
print("cache_warm_const_edit: %s" % ("ok" if not fails else "%d stale" % fails))
sys.exit(1 if fails else 0)
