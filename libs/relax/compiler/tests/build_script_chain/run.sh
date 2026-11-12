#!/bin/sh
# relax run on the fixture: a three-level build-dependency chain (app -> helper_a -> helper_b),
# each with its own build script. Prints `scan=b`, as `cargo run` does.
# Usage: run.sh <relax binary> [run flags]
set -eu
here=$(cd "$(dirname "$0")" && pwd)
m=$1
shift
cd "$here"
export CARGO_NET_OFFLINE=true CARGO_INCREMENTAL=0
exec nice -n 15 "$m" run "$@" app
