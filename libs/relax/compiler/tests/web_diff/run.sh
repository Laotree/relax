#!/bin/bash
# run.sh <makepad/relax binary> <w32|w64> [workdir]: web_diff.rs under Relax's web target against
# rustc's build of it: wasm32 = a wasm32-unknown-unknown cdylib run in node (host.js); wasm64 = a
# host binary (wasm64's data layout is x86_64's). Prints "web_diff <w>: N lines equal" or the diff.
set -u
H=$(cd "$(dirname "$0")" && pwd)
B=$1
W=$2
T=${3:-$(mktemp -d)}
mkdir -p "$T/u"
case "$W" in
  w32) TRIPLE=wasm32-unknown-unknown
       if [ -n "${REF:-}" ]; then cp "$REF" "$T/ref.txt"; else
       rustc --edition 2021 -O --target wasm32-unknown-unknown --crate-type cdylib -C link-arg=--allow-undefined "$H/web_diff.rs" -o "$T/ref.wasm" 2>"$T/rustc.err" || { cat "$T/rustc.err"; exit 2; }
       node "$H/host.js" "$T/ref.wasm" 2> "$T/ref.txt" || exit 2; fi ;;
  w64) TRIPLE=wasm64-unknown-unknown
       if [ -n "${REF:-}" ]; then cp "$REF" "$T/ref.txt"; else
       rustc --edition 2021 -O "$H/web_diff.rs" -o "$T/ref" 2>"$T/rustc.err" || { cat "$T/rustc.err"; exit 2; }
       "$T/ref" 2> "$T/ref.txt" || exit 2; fi ;;
  *) echo "usage: run.sh <binary> <w32|w64> [workdir]"; exit 2 ;;
esac
cat > "$T/u/units.json" <<J
{"version":1,"roots":[0],"units":[{"pkg_id":"path+file://$T#web_diff@0.0.0","target":{"kind":["bin"],"name":"web_diff","src_path":"$H/web_diff.rs","edition":"2021"},"mode":"build","features":[],"dependencies":[]}]}
J
MAKEPAD_RUN_CHECK_TARGET=$TRIPLE MAKEPAD_RUN_STD=$H/../../std MAKEPAD_RUN_CACHE_DIR=$T/tgt "$B" run --quiet --no-live --units "$T/u/units.json" web_diff > "$T/relax.out" 2> "$T/relax.err"
grep -v "^makepad\|^  /" "$T/relax.err" > "$T/relax.txt"
if diff "$T/ref.txt" "$T/relax.txt" > "$T/diff"; then
  echo "web_diff $W: $(wc -l < "$T/ref.txt" | tr -d ' ') lines equal"
else
  head -40 "$T/diff"
  grep "^makepad" "$T/relax.err" | cut -c1-300 | head -5
  echo "web_diff $W: DIFFERENT (log $T/relax.err)"
  exit 1
fi
