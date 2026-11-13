#!/bin/sh
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
binary=$1
cd "$here"
exec "$binary" test non-unicode-launch
