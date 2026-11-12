#!/bin/sh
# relax run on the fixture: `wrapper`'s `fast` feature asks for `extra/boost`, which must enable
# wrapper's own `extra` feature (hidden implicit) so `boosted()` compiles. Prints `42`.
# Usage: run.sh <relax binary> [run flags]
set -eu
here=$(cd "$(dirname "$0")" && pwd)
m=$1
shift
cd "$here"
export CARGO_NET_OFFLINE=true CARGO_INCREMENTAL=0
exec nice -n 15 "$m" run "$@" app
