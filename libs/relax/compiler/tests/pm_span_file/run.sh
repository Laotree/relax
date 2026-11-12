#!/bin/bash
# usage: run.sh <makepad binary>: a proc macro that calls Span::call_site().file() and .local_file()
# (stable since 1.88; askama_derive 0.16 does) compiles and runs. Prints "pm_span_file: ok" or
# "pm_span_file: FAILED" (exit 1).
H=$(cd "$(dirname "$0")" && pwd)
T=$(mktemp -d)
WANT="local_file ok"
OUT=$(cd "$H" && MAKEPAD_RUN_STD=$H/../../std MAKEPAD_HOME=$T/home MAKEPAD_RUN_HOME=$T MAKEPAD_RUN_CACHE_DIR=$T/cache MAKEPAD_RUN_TARGET_DIR=$T/target "$1" run --quiet pmsf-app 2>>"$T/err")
echo "run: $OUT"
ok=0
[ "$OUT" = "$WANT" ] && ok=1
[ $ok = 1 ] || tail -5 "$T/err"
rm -rf "$T"
if [ $ok = 1 ]; then echo "pm_span_file: ok"; else echo "pm_span_file: FAILED"; exit 1; fi
