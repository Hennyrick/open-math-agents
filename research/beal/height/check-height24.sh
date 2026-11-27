#!/usr/bin/env bash
# Replay with Lean 4.33.1. Only its standard library is needed.
set -euo pipefail
cd "$(dirname "$0")"
build_dir="${BEAL_HEIGHT_BUILD:-$PWD/.height24-build}"
lean_cmd="${LEAN:-lean}"
mkdir -p "$build_dir/Height24"
export LEAN_PATH="$build_dir${LEAN_PATH:+:$LEAN_PATH}"

compile() {
  local module="$1"
  shift
  local target="$build_dir/$module.olean" log="$build_dir/$module.log"
  local needs_compile=false dep
  if [[ ! -s "$target" || "$module.lean" -nt "$target" ]]; then
    needs_compile=true
  fi
  for dep in "$@"; do
    if [[ "$build_dir/$dep.olean" -nt "$target" ]]; then
      needs_compile=true
    fi
  done

  if [[ "$needs_compile" == true ]]; then
    echo "Checking $module"
    if ! "$lean_cmd" -j1 -DmaxHeartbeats=0 -DmaxRecDepth=30000 -M3000 \
        -o "$target.tmp" "$module.lean" >"$log" 2>&1; then
      cat "$log" >&2
      rm -f "$target.tmp"
      return 1
    fi
    mv "$target.tmp" "$target"
  fi
}

compile Bounded
compile Height24/Data Bounded
compile Height24/Enumeration Height24/Data
groups=(Height24/Rows{0..6})
for ((i=0; i<${#groups[@]}; i+=3)); do
  pids=()
  for module in "${groups[@]:i:3}"; do
    compile "$module" Height24/Data &
    pids+=("$!")
  done
  exit_status=0
  for pid in "${pids[@]}"; do
    wait "$pid" || exit_status=1
  done
  if ((exit_status)); then exit 1; fi
done

compile Height24 Height24/Enumeration "${groups[@]}"
# Query the cached, re-imported theorem on every invocation.
"$lean_cmd" --stdin <<'LEAN'
import Height24
#check BealHeight.TwoTo24.checked
#print axioms BealHeight.TwoTo24.checked
LEAN
