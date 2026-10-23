#!/usr/bin/env python3
"""Invalidated code never runs again (INVALID, invalid.rs), end to end in `makepad run`.

usage: run.py --makepad <makepad binary>   (MAKEPAD_RUN_STD in the environment)

Copies pkg/ to a temporary dir, runs it live with MAKEPAD_RUN_STALE_PARK=1 and edits src/work.rs:
  1. body edit (patch gen 1): step() now calls park_here -> the worker blocks inside gen 1's step
  2. layout edit (gen 2): State gets a field   -> gen 1's step is invalidated (PROT_NONE) while the
                                                 worker's frame is in it; `stale` lists the range
  3. free the worker                            -> it returns into invalidated code: parked, the app
                                                 pauses; `stale` says RETURNED, the layout patch,
                                                 the patch events, every stack (INVALIDATED frame)
  4. resume restart                             -> the process starts again on the current source
  5. an edit the borrow checker rejects after it ran (SPEC-V), the worker blocked inside it
                                                -> REVERTED: its code is invalidated
  6. free the worker                            -> parked again (reason: the borrow checker)
  7. resume stop                                -> the process ends by the signal
Prints PASS/FAIL per step; exit 1 on any FAIL.
"""
import os, re, shutil, subprocess, sys, tempfile, threading, time

HERE = os.path.dirname(os.path.abspath(__file__))
mk = os.path.abspath(sys.argv[sys.argv.index("--makepad") + 1])
tmp = tempfile.mkdtemp(prefix="live-invalid-")
pkg = os.path.join(tmp, "pkg")
shutil.copytree(os.path.join(HERE, "pkg"), pkg)
work = os.path.join(pkg, "src", "work.rs")
base = open(work).read()
env = dict(os.environ, MAKEPAD_RUN_CACHE="0", MAKEPAD_RUN_STALE_PARK="1")
p = subprocess.Popen([mk, "run", "--quiet", "relax-live-invalid"], cwd=pkg, env=env, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
out, err = [], []
def pump(f, acc):
    for line in f:
        acc.append(line.rstrip("\n"))
threading.Thread(target=pump, args=(p.stdout, out), daemon=True).start()
threading.Thread(target=pump, args=(p.stderr, err), daemon=True).start()

def wait(pred, secs=30):
    t = time.time()
    while time.time() - t < secs:
        if pred():
            return True
        time.sleep(0.05)
    return False

def save(text):
    with open(work, "w") as f:
        f.write(text)
    st = os.stat(work)
    os.utime(work, ns=(st.st_atime_ns, st.st_mtime_ns + 1_000_000))

def send(cmd):
    p.stdin.write(cmd + "\n")
    p.stdin.flush()

def inspect(*args):
    r = subprocess.run([mk, "inspect", str(p.pid), *args], capture_output=True, text=True, timeout=90)
    return r.stdout + r.stderr

def since(acc, n, pat):
    return any(re.search(pat, l) for l in acc[n:])

def parked_id(n):
    for l in err[n:]:
        m = re.search(r"stale access parked as (P\d+)", l)
        if m:
            return m.group(1)
    return None

fails = 0
def step(name, ok, detail=""):
    global fails
    print("%s %s" % ("PASS" if ok else "FAIL", name))
    if not ok:
        fails += 1
        if detail:
            print("  " + detail[:3000].replace("\n", "\n  "))

def body(code):
    return base.replace("""    s.a = s.a.wrapping_add(n & 1);
    10""", code)

try:
    step("starts", wait(lambda: any(l.startswith("out tick 0 10") for l in out), 180))
    # 1. gen 1: step parks inside its own (patched) code
    n_out, n_err = len(out), len(err)
    gen1 = body("""    let g = crate::park_here(n);
    s.a = s.a.wrapping_add(g & 1);
    20""")
    save(gen1)
    step("body edit applies; the worker blocks inside the patched step", wait(lambda: since(out, n_out, r"^out parked \d+$") and since(err, n_err, "patched")))
    # 2. gen 2: a layout edit replaces it while the worker's frame is in it
    n_err = len(err)
    layout = gen1.replace("    pub a: u64,\n", "    pub a: u64,\n    pub b: u64,\n").replace("State { a: 1 }", "State { a: 1, b: 0 }")
    layout = layout.replace("""    let g = crate::park_here(n);
    s.a = s.a.wrapping_add(g & 1);
    20""", """    s.b = s.b.wrapping_add(1);
    s.a = s.a.wrapping_add(n & 1);
    30""")
    save(layout)
    ok = wait(lambda: since(err, n_err, "patched"))
    told = inspect("stale")
    step("layout edit applies; gen 1's step is invalidated (listed in stale)", ok and "invalidated code `" in told and "work::step" in told and "layout-changing patch gen 2" in told, told + "\n".join(err[-20:]))
    code = inspect("code")
    step("inspect code counts the invalidated group", "invalidated (PROT_NONE, never reused): 1 groups" in code or re.search(r"invalidated \(PROT_NONE, never reused\): [1-9]\d* groups", code) is not None, code)
    # 3. the worker returns into it: parked, paused
    n_err = len(err)
    send("free")
    ok = wait(lambda: parked_id(n_err) is not None)
    pid1 = parked_id(n_err)
    step("the return into invalidated code parks the thread (%s)" % pid1, ok and since(err, n_err, r"stale access into the invalidated code `[^`]*work::step"), "\n".join(err[n_err:][-30:]))
    told = inspect("stale")
    step("stale: RETURNED, version, reason, both patch events, stacks with the INVALIDATED frame",
         "RETURNED into" in told and "layout-changing patch gen 2" in told and "made by flightrec reload.patch" in told and "invalidated by flightrec reload.patch" in told and "INVALIDATED" in told and "work::step" in told, told)
    listed = inspect("panics")
    step("listed as a parked stale access", (pid1 or "?") in listed and "stale access" in listed, listed)
    time.sleep(0.5)
    step("the process waits for a decision", p.poll() is None)
    # 4. restart: the process runs again from the current source
    n_out, n_err = len(out), len(err)
    r = inspect("resume", pid1 or "P0", "restart")
    ok = wait(lambda: since(out, n_out, "^out start$") and since(out, n_out, r"^out tick \d+ 30$"), 180)
    step("resume restart: the process starts again on the current source", ok and "process restart" in r, r + "\n".join(err[n_err:][-20:]))
    # 5. SPEC-V: an edit the borrow checker rejects after it ran, the worker blocked inside it
    n_out, n_err = len(out), len(err)
    rejected = layout.replace("""    s.b = s.b.wrapping_add(1);
    s.a = s.a.wrapping_add(n & 1);
    30""", """    let g = crate::park_here(n + 1000000);
    let mut v = vec![s.a, g];
    let r = &v[0];
    v.push(s.b);
    *r + 40""")
    save(rejected)
    ok = wait(lambda: since(out, n_out, r"^out parked 1\d{6}$") and since(err, n_err, "REVERTED"), 60)
    step("rejected edit ran (worker inside it) and was REVERTED", ok, "\n".join(out[n_out:][-10:] + err[n_err:][-30:]))
    told = inspect("stale")
    step("its code is invalidated (borrow checker)", "rolled back: the borrow checker rejected it" in told, told)
    # 6. the worker returns into it
    n_err = len(err)
    send("free")
    ok = wait(lambda: parked_id(n_err) is not None)
    pid2 = parked_id(n_err)
    told = inspect("stale")
    step("the return into the rejected code parks (%s)" % pid2, ok and "RETURNED into" in told and "the borrow checker rejected it" in told, told + "\n".join(err[n_err:][-30:]))
    # 7. stop
    inspect("resume", pid2 or "P0", "stop")
    ok = wait(lambda: p.poll() is not None, 30)
    step("resume stop ends the process (status %s)" % p.poll(), ok and p.poll() != 0)
finally:
    if p.poll() is None:
        p.kill()
if fails:
    print("---- stderr"); print("\n".join(err[-60:]))
    print("---- stdout"); print("\n".join(out[-20:]))
shutil.rmtree(tmp, ignore_errors=True)
print("live invalid: %d fail" % fails)
sys.exit(1 if fails else 0)
