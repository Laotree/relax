#!/bin/bash
# Usage: bash run_live_regressions.sh <relax binary>
# `relax test` runs assertions but background borrowck errors do not fail it.
# Check these fixtures synchronously so strict borrowck errors fail the suite.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
BIN=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
export RELAX_CACHE=off RELAX_BORROWCK=full RELAX_GANDALF=0
export RELAX_STD="$HERE/../../std" RELAX_CACHE_DIR="$TMP/target"
unset RELAX_RELAXED RELAX_BORROWCK_ALL RELAX_BORROWCK_ONLY RELAX_BORROWCK_INSTANCES
for name in dyn_any_ptr_cast_accept never_deref_move_accept generic_call_once_accept generic_call_mut_reject raw_ptr_capture_accept raw_ptr_capture_reject closure_external_mutex_accept closure_external_downcast_accept closure_external_reborrow_accept closure_external_field_accept closure_external_nested_accept closure_external_named_accept closure_external_distinct_reject ref_reuse_accept; do
    python3 - "$TMP" "$HERE" "$name" <<'PY'
import json, pathlib, sys
tmp, here, name = sys.argv[1:]
unit = {"pkg_id": f"path+file://{tmp}#{name}@0.0.0",
        "target": {"kind": ["bin"], "name": name,
                   "src_path": f"{here}/{name}.rs", "edition": "2021"},
        "mode": "build", "features": [], "dependencies": []}
pathlib.Path(tmp, "units.json").write_text(json.dumps(
    {"version": 1, "roots": [0], "units": [unit]}))
PY
    if [[ "$name" == closure_external_distinct_reject ]]; then
        if rustc --edition 2021 "$HERE/$name.rs" -o "$TMP/rustc" > "$TMP/rustc.log" 2>&1 ||
           ! grep -q 'lifetime may not live long enough' "$TMP/rustc.log"; then
            cat "$TMP/rustc.log"
            exit 1
        fi
        if "$BIN" check --no-serve --units "$TMP/units.json" "$name" > "$TMP/check.log" 2>&1 ||
           ! grep -q "must outlive" "$TMP/check.log"; then
            cat "$TMP/check.log"
            exit 1
        fi
        echo "$name: ok (rustc and Relax reject the parent lifetime requirement)"
        continue
    fi
    if [[ "$name" == ref_reuse_accept ]]; then
        # generic bodies polymorphically, as Gandalf checks them while a program runs (that
        # mode prints only the errors: exit status 0 and none printed)
        rustc --edition 2021 "$HERE/$name.rs" -o "$TMP/rustc" > "$TMP/rustc.log" 2>&1 || {
            cat "$TMP/rustc.log"
            exit 1
        }
        if ! RELAX_BORROWCK_ALL=1 "$BIN" check --no-serve --units "$TMP/units.json" "$name" > "$TMP/check.log" 2>&1 ||
           grep -Eq 'error\[|panicked at' "$TMP/check.log"; then
            cat "$TMP/check.log"
            exit 1
        fi
        echo "$name: ok (generic bodies checked polymorphically)"
        continue
    fi
    if [[ "$name" == closure_external_* ]]; then
        rustc --edition 2021 "$HERE/$name.rs" -o "$TMP/rustc" > "$TMP/rustc.log" 2>&1 || {
            cat "$TMP/rustc.log"
            exit 1
        }
        "$TMP/rustc"
    fi
    if [[ "$name" == generic_call_* || "$name" == raw_ptr_capture_* ]]; then
        export RELAX_BORROWCK_INSTANCES=1
        if [[ "$name" == *_reject ]]; then
            code=E0596
            if [[ "$name" == raw_ptr_capture_* ]]; then code=E0382; fi
            if rustc --edition 2021 "$HERE/$name.rs" -o "$TMP/rustc" > "$TMP/rustc.log" 2>&1 ||
               ! grep -q "$code" "$TMP/rustc.log"; then
                cat "$TMP/rustc.log"
                exit 1
            fi
            if "$BIN" check --no-serve --units "$TMP/units.json" "$name" > "$TMP/check.log" 2>&1 ||
               ! grep -q "error\[$code\]" "$TMP/check.log"; then
                cat "$TMP/check.log"
                exit 1
            fi
            echo "$name: ok (rustc and Relax reject with $code)"
            continue
        fi
        rustc --edition 2021 "$HERE/$name.rs" -o "$TMP/rustc"
        "$TMP/rustc"
    fi
    if ! "$BIN" check --no-serve --units "$TMP/units.json" "$name" > "$TMP/check.log" 2>&1; then
        cat "$TMP/check.log"
        exit 1
    fi
    if ! grep -q 'relax-check: .* 0 errors' "$TMP/check.log" ||
       grep -Eq 'panicked at|borrowck unchecked|internal error in the borrow checker' "$TMP/check.log"; then
        cat "$TMP/check.log"
        exit 1
    fi
    echo "$name: ok"
done
