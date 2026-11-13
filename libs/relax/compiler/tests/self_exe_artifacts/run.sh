#!/bin/bash
set -eu
H=$(cd "$(dirname "$0")" && pwd)
cd "$H"
LOG=$(mktemp)
trap 'rm -f "$LOG"' EXIT
RELAX_STD="$H/../../std" "$1" test self-exe-artifacts >"$LOG" 2>&1 || { cat "$LOG"; exit 1; }
cat "$LOG"
passed() {
  grep -Fqx "test $1 ... ok" "$LOG" || { echo "self_exe_artifacts: $1 did not pass"; exit 1; }
}
passed package_binary_beside_test_artifacts
passed self_through_another_program
passed cargo_binary_launch
case "$(uname -s)" in
  MINGW*|MSYS*|CYGWIN*) ;;
  *)
    passed self_through_shell
    passed self_after_loader_replaced
    mkdir -p "$H/target"
    COPY=$(mktemp -d "$H/target/self-loader.XXXXXX")
    trap 'rm -f "$LOG"; rm -r "$COPY"' EXIT
    cp "$1" "$COPY/loader"
    SELF_EXE_REPLACE_LOADER="$COPY/loader" RELAX_STD="$H/../../std" "$COPY/loader" test self-exe-artifacts --test identity -- --exact self_after_loader_replaced >"$LOG" 2>&1 || { cat "$LOG"; exit 1; }
    cat "$LOG"
    passed self_after_loader_replaced
    for mode in direct shell; do
      if [ "$mode" = shell ]; then export SELF_EXE_EXEC_SHELL=1; else unset SELF_EXE_EXEC_SHELL; fi
      RELAX_STD="$H/../../std" "$1" test self-exe-artifacts --test identity -- --ignored --exact self_after_exec >"$LOG" 2>&1 || { cat "$LOG"; exit 1; }
      cat "$LOG"
      passed self_after_exec
    done
    ;;
esac
