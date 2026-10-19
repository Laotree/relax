#!/usr/bin/env python3
"""usage: run.py <makepad binary> [scenario ...]: code-cache sharing between apps, and the stale hits it must not make.

One workspace (fw = the shared framework crate; app_a/app_c use fw with feature `fast`, app_b without, app_p adds a
crate the loader binds). Each scenario: a fresh copy of the tree and a fresh disk cache; the FIRST app runs cold, an
optional edit is applied, the SECOND app runs on the same cache. Checks: (1) the second app's output equals the output
of the same app on the same (edited) tree with an empty cache; (2) the fw fns that must hit do, the fns the edit or the
feature difference reaches are compiled again. Prints "cache_shared_apps <scenario>: ok|FAILED ..." per scenario;
exits 1 on a failure."""
import os, re, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.normpath(os.path.join(HERE, "..", "..", "..", "..", ".."))
STD = os.path.normpath(os.path.join(HERE, "..", "..", "std"))
# fw fns that no scenario's edit or feature difference reaches (the plain ones)
PLAIN = ["unrelated", "uses_unrelated", "area", "sum_to", "add"]
# name: (first app, second app, edit (file, old, new) or None, hit in 2nd, compiled in 2nd, std edit or None)
MIN_HITS = {"provided": 100}
SCENARIOS = {
    # same fw features, another app: the framework's code is shared
    "share": ("app_a", "app_c", None, PLAIN + ["from_macro", "describe", "cfg_macro", "gated"], [], None),
    # the first app holds a crate the loader binds (the provided-crate fixture, run from the repository's own workspace), the
    # second does not: the std code both compile is shared (at least MIN_HITS slots)
    "provided": ("repo:relax-provided-fixture", "app_b", None, [], [], None),
    # fw built with feature `fast` by one app, without by the other: what reads the feature is never shared
    "features": ("app_a", "app_b", None, [], ["cfg_macro", "gated"], None),
    # a fn body of the shared crate edited between the two apps
    "body": ("app_a", "app_c", ("fw/src/lib.rs", "pub fn add(a: u32, b: u32) -> u32 { a + b } // EDIT add", "pub fn add(a: u32, b: u32) -> u32 { a + b + 100 } // EDIT add"),
             [x for x in PLAIN if x != "add"] + ["from_macro", "describe"], ["add"], None),
    # an item macro's invocation edited
    "macro": ("app_a", "app_c", ("fw/src/lib.rs", "mk_fn!(from_macro = 40); // EDIT macro", "mk_fn!(from_macro = 41); // EDIT macro"),
              [x for x in PLAIN] + ["describe"], ["from_macro"], None),
    # a struct layout of the shared crate: its users are compiled again, the rest is shared
    "layout": ("app_a", "app_c", ("fw/src/lib.rs", "pub struct Shape { pub w: u32, pub h: u32 } // EDIT shape", "pub struct Shape { pub w: u32, pub h: u32, pub d: u64 } // EDIT shape"),
               [], ["area", "describe"], None),
    # a std fn body edited between the two apps (the std source is part of every crate's identity: sum_from compiles again)
    "std_body": ("app_a", "app_c", None, [], ["sum_from"],
                 ("core/iter/mod.rs", "    iter.fold(zero, |a, b| a + b)\n", "    iter.fold(zero, |a, b| b + a)\n")),
    # a std interface edit (a const fn body is part of the interface): everything above core is compiled again
    "std_iface": ("app_a", "app_c", None, [], PLAIN,
                  ("core/num/int_impls.rs", "    pub const fn pow(self, exp: u32) -> u32 { self.wrapping_pow(exp) }", "    pub const fn pow(self, exp: u32) -> u32 { self.wrapping_pow(exp) + 0 }")),
}


def run(relax, tree, std, cache, app, tag):
    if app.startswith("repo:"):
        tree, pkg = REPO, app[5:]
    else:
        pkg = "sc-" + app.replace("_", "-")
    env = dict(os.environ, MAKEPAD_RUN_CACHE_DIR=os.path.join(cache, "cache"), MAKEPAD_RUN_STD=std, RUSTC_BOOTSTRAP="1",
               MAKEPAD_RUN_CACHE_TRACE=os.path.join(cache, tag + ".trace"))
    env.pop("MAKEPAD_RUN_CACHE", None)
    p = subprocess.run([relax, "run", "--quiet", pkg], cwd=tree, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=900)
    out = p.stdout.decode("utf-8", "replace")
    open(os.path.join(cache, tag + ".log"), "w").write(out)
    m = re.search(r"shared_apps result ([0-9 ]+)", out)
    res = m.group(1).strip() if m else None
    trace = {}
    try:
        for line in open(os.path.join(cache, tag + ".trace"), errors="replace"):
            f = line.rstrip("\n").split("\t")
            if len(f) >= 6:
                trace.setdefault(f[5], set()).add(f[1])
    except FileNotFoundError:
        pass
    return p.returncode, res, out, trace


def status(trace, name):
    """'hit', 'compiled' or None for the fw fns called `name`"""
    seen = set()
    for slot, whats in trace.items():
        if slot.startswith("sc_fw::") and re.search(r"::(" + re.escape(name) + r")(,|$)", slot):
            seen |= whats
        elif name in ("sum_from",) and re.search(r"::sum_from(,|$)", slot):
            seen |= whats
    if seen & {"miss", "linkfail", "cert:stale", "cert:undecodable"}:
        return "compiled"
    if seen & {"hit"}:
        return "hit"
    return None


def edit_file(path, old, new):
    text = open(path).read()
    assert text.count(old) == 1, (path, old)
    open(path, "w").write(text.replace(old, new))


def scenario(relax, name):
    first, second, edit, hit, compiled, stdedit = SCENARIOS[name]
    tmp = tempfile.mkdtemp(prefix="relax-cache-shared-apps-")
    bad = []
    try:
        tree = os.path.join(tmp, "tree")
        shutil.copytree(HERE, tree, ignore=shutil.ignore_patterns("run.py", "target", "__pycache__"))
        shutil.copytree(STD, os.path.join(tmp, "std"))
        std = os.path.join(tmp, "std")
        cache = os.path.join(tmp, "c")
        os.mkdir(cache, 0o700)
        rc, res1, out, _ = run(relax, tree, std, cache, first, "1-first")
        if rc != 0 or (res1 is None and not first.startswith("repo:")):
            bad.append(f"first app: exit {rc}, no result\n{out[-600:]}")
        if edit:
            edit_file(os.path.join(tree, edit[0]), edit[1], edit[2])
        if stdedit:
            edit_file(os.path.join(std, stdedit[0]), stdedit[1], stdedit[2])
        rc, res2, out, tr = run(relax, tree, std, cache, second, "2-second")
        ref = os.path.join(tmp, "ref")
        os.mkdir(ref, 0o700)
        rc0, want, out0, _ = run(relax, tree, std, ref, second, "ref")
        if rc != 0 or res2 is None or res2 != want:
            bad.append(f"second app (shared cache): exit {rc}, result {res2}; empty cache gives {want} (exit {rc0})")
        if MIN_HITS.get(name, 0) > sum(1 for w in tr.values() if "hit" in w):
            bad.append(f"fewer than {MIN_HITS[name]} slots shared")
        for f in hit:
            if status(tr, f) != "hit":
                bad.append(f"{f} should be shared but was {status(tr, f)}")
        for f in compiled:
            if status(tr, f) == "hit":
                bad.append(f"{f} was linked from the cache but must be compiled again")
        n_hit = sum(1 for w in tr.values() if "hit" in w)
        n_miss = sum(1 for w in tr.values() if w & {"miss", "linkfail", "cert:stale"})
        print(f"cache_shared_apps {name}: " + ("ok" if not bad else "FAILED " + "; ".join(bad)) + f" ({first} then {second}: {n_hit} slots linked, {n_miss} compiled)", flush=True)
    finally:
        if not bad and os.path.basename(tmp).startswith("relax-cache-shared-apps-"):
            shutil.rmtree(tmp)
        elif bad:
            print(f"  logs kept in {tmp}", flush=True)
    return not bad


def main():
    relax = os.path.abspath(sys.argv[1])
    names = sys.argv[2:] or list(SCENARIOS)
    ok = all([scenario(relax, n) for n in names])
    sys.exit(0 if ok else 1)


main()
