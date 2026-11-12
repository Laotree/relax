#!/bin/sh
# relax check on the fixture without --allow-c, after one `--allow-c` run: the build script's
# own child run reads the native outputs and library the parent built.
# Usage: run.sh <relax binary> [check flags]
set -eu
here=$(cd "$(dirname "$0")" && pwd)
m=$1
shift
cd "$here"
export CARGO_NET_OFFLINE=true CARGO_INCREMENTAL=0
exec nice -n 15 "$m" check "$@" app
