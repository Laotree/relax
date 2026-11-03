#!/bin/bash
# usage: run.sh <makepad binary>: under `makepad test --live`, an edit of a provided crate (one built
# into the makepad binary) is answered at once: one patchrefused per save, "needs a JIT rebuild",
# never a session stuck in "patching" (WORKPOOL's makepad-hal struct edit hung 14 min). The binary
# runs from a copy outside any cargo target directory, as devhub's boxes run theirs: it cannot
# rebuild itself there. The crate is a byte-identical copy of tools/run/fixture
# (relax-provided-fixture), so the copy's source identity is the one built in.
set -u
H=$(cd "$(dirname "$0")" && pwd)
R=$(cd "$H/../../../../.." && pwd)
T=$(mktemp -d "${TMPDIR:-/tmp}/live_provided.XXXXXX") || exit 1
: "${T:?}"
pid=""
jit=""
finish() {
    [ -n "$jit" ] && kill "$jit" 2>/dev/null
    [ -n "$pid" ] && kill "$pid" 2>/dev/null
    [ -n "$pid" ] && wait "$pid" 2>/dev/null
    rm -rf "$T"
}
trap finish EXIT
mkdir -p "$T/ws/fixture" "$T/home" "$T/tmp"
cp "$1" "$T/makepad" || exit 1
cp -R "$R/tools/run/fixture/Cargo.toml" "$R/tools/run/fixture/src" "$R/tools/run/fixture/tests" "$T/ws/fixture/"
cat > "$T/ws/Cargo.toml" <<EOF
[workspace]
members = ["fixture"]
resolver = "2"

[workspace.dependencies]
makepad-relax-api = { path = "$R/libs/relax_api" }
EOF
export MAKEPAD_RUN_CACHE=off MAKEPAD_RUN_HOME="$T/home" TMPDIR="$T/tmp"
unset MAKEPAD_RUN_STD
(cd "$T/ws" && exec "$T/makepad" test --live relax-provided-fixture --test relax_api_entries) > "$T/log" 2>&1 &
pid=$!
fail() { echo "live_provided_edit: FAILED ($1)"; tail -20 "$T/log"; exit 1; }
# the initial run's verdict
for _ in $(seq 1 600); do
    grep -q '^testverdict group=0' "$T/log" && break
    kill -0 "$pid" 2>/dev/null || fail "the session ended before its first verdict"
    sleep 0.5
done
grep -q '^testverdict group=0' "$T/log" || fail "no initial verdict in 300 s"
jit=$(sed -n 's/^makepad-remote: pid \([0-9]*\) .*/\1/p' "$T/log" | head -1)
[ -n "$jit" ] || fail "no inspect socket line"
lib="$T/ws/fixture/src/lib.rs"
# the next patch event comes within 10 s of the edit and refuses it ($1), saying $3; $2: the
# watch's start (empty: from now, started before the edit is made)
since=""
watch() {
    "$T/makepad" inspect "$jit" watch on=patchrefused,patchverified timeout_s=15 --json ${1:+since=$1} > "$T/watch" 2>&1
}
refusal() {
    out=$(cat "$T/watch")
    echo "$out" | grep -q '"event":"patchrefused"' || fail "$1: no patchrefused: $out"
    echo "$out" | grep -q '"outcome":"refused"' || fail "$1: not refused: $out"
    echo "$out" | grep -q "$3" || fail "$1: the reason does not say '$3': $out"
    [ $(($(date +%s) - $2)) -le 10 ] || fail "$1: answered after $(($(date +%s) - $2)) s"
    since=$(echo "$out" | sed -n 's/.*"rearm":"watch since=\([0-9]*\)".*/\1/p' | tail -1)
}
watch & w=$!
sleep 1
# a layout edit of a provided crate: a field more in `P`
t0=$(date +%s)
perl -pi -e 's/^pub struct P \{$/pub struct P {\n    pub added: u64,/' "$lib"
grep -q 'pub added: u64' "$lib" || fail "the edit did not apply"
wait $w
refusal layout "$t0" 'needs a JIT rebuild'
# a save after it: answered too (the restart it waits for is pending)
t0=$(date +%s)
perl -pi -e 's/pub added: u64,/pub added: u32,/' "$lib"
watch "$since"
refusal later "$t0" 'restart pending'
kill -0 "$pid" 2>/dev/null || fail "the session ended"
echo "live_provided_edit: ok"
