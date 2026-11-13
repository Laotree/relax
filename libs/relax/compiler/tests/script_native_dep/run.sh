#!/bin/bash
# usage: run.sh <makepad binary>: `makepad run --allow-c snd-app`, whose build script has a native
# build-dependency (plain C) and whose program a native dependency whose C calls back into its
# own Rust. The run links both packages into one native library and the build script's run loads
# it: the callback is no fn of the script's program, which never calls that C, so the script runs
# and the program prints what cargo's does (relax issue 174). One line per case; the last is
# "script_native_dep: ok" or "script_native_dep: FAILED" (exit 1).
H=$(cd "$(dirname "$0")" && pwd)
T=$(mktemp -d)
[ -n "$T" ] && [ -d "$T" ] || exit 2
trap 'rm -rf "$T"' EXIT
export RELAX_CACHE=off CARGO_NET_OFFLINE=true CARGO_TARGET_DIR=$T/target RELAX_PANIC_PARK=0
export RELAX_STD=$H/../../std
FAILS=0
case_is() { # name ok?
    if [ "$2" = 1 ]; then echo "script_native_dep: $1: ok"; else echo "script_native_dep: $1: FAILED"; FAILS=$((FAILS + 1)); fi
}
OUT=$(cd "$H" && "$1" run --quiet --allow-c snd-app 2>&1)
rc=$?
echo "$OUT" | tail -5
ok=0
[ $rc = 0 ] && echo "$OUT" | grep -qx "script 42 program 41" && ok=1
case_is "a build script with a native build-dependency" $ok
if [ $FAILS = 0 ]; then echo "script_native_dep: ok"; else echo "script_native_dep: FAILED ($FAILS)"; exit 1; fi
