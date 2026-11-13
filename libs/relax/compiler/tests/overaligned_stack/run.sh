#!/bin/bash
H=$(cd "$(dirname "$0")" && pwd) || exit 1
OUT=$(cd "$H" && RELAX_STD="$H/../../std" "$1" test overaligned_stack 2>&1)
rc=$?
printf '%s\n' "$OUT"
if [ "$rc" != 0 ] || ! printf '%s\n' "$OUT" | grep -q '^test result: ok. 7 passed; 0 failed;'; then
    echo 'overaligned_stack: FAILED'
    exit 1
fi
echo 'overaligned_stack: ok'
