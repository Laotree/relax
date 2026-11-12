#!/bin/bash
# usage: run.sh <relax binary>: a build script of a package that declares `links` sees
# CARGO_MANIFEST_LINKS, as under cargo. Prints "manifest_links_env: ok" or
# "manifest_links_env: FAILED" (exit 1).
H=$(cd "$(dirname "$0")" && pwd)
export MAKEPAD_RUN_CACHE=off
ERR=$(mktemp)
A=$(cd "$H" && MAKEPAD_RUN_STD=$H/../../std "$1" run --quiet mle-app 2>"$ERR")
echo "$A"
if [ "$A" = "links = mle_probe" ]; then
  rm -f "$ERR"; echo "manifest_links_env: ok"
else
  tail -5 "$ERR"; rm -f "$ERR"; echo "manifest_links_env: FAILED"; exit 1
fi
