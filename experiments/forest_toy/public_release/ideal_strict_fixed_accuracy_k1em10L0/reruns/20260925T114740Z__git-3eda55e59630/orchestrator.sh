#!/usr/bin/env bash
set -euo pipefail

# This orchestration layer is intentionally separate from the frozen experiment
# source.  It waits for the full parent rerun, then performs the strict random
# search and renders both paper layouts from exactly that fresh parent output.
run_root="/home/kawata/work/uen_forest_toy_fresh_reruns/20260925T114740Z__git-3eda55e59630"
bundle="$run_root/source/experiments/forest_toy/public_release/ideal_strict_fixed_accuracy_k1em10L0"
python_bin="/home/kawata/work/uen_forest_toy_robustness_20260919/.venv/bin/python"
parent_output="$bundle/results/ideal_capless_fixed_accuracy_scaling"
strict_output="$run_root/strict_random"
reference_output="$run_root/bundled_reference_results/random_per_run_threshold_search_k1em10L0"

export OPENBLAS_NUM_THREADS=1
export OMP_NUM_THREADS=1
export MKL_NUM_THREADS=1
export NUMEXPR_NUM_THREADS=1
export PYTHONUNBUFFERED=1
export PYTHONPYCACHEPREFIX=/tmp/uen_4forest_20260925_pycache
export MPLCONFIGDIR=/tmp/uen_4forest_20260925_mpl

record_failure() {
  code=$?
  printf '%s exit=%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$code" \
    > "$run_root/pipeline_failed.txt"
  exit "$code"
}
trap record_failure ERR

parent_pid="$(cat "$run_root/full_parent.pid")"
while kill -0 "$parent_pid" 2>/dev/null; do
  sleep 30
done

"$python_bin" - "$parent_output/status.json" <<'PY'
import json
from pathlib import Path
import sys

status = json.loads(Path(sys.argv[1]).read_text())
if status.get("status") != "complete":
    raise SystemExit(f"Parent rerun did not complete: {status}")
PY

cd "$bundle"
"$python_bin" -B random_per_run_threshold_search.py \
  --workers 8 \
  --threshold-scale 1e-7 \
  --output "$strict_output" \
  > "$run_root/strict_random.log" 2>&1

"$python_bin" -B report_ideal_strict_fixed_accuracy_1x4.py \
  --results "$strict_output" \
  > "$run_root/render_standard.log" 2>&1

"$python_bin" -B report_ideal_strict_fixed_accuracy_1x4.py \
  --large-text \
  --results "$strict_output" \
  > "$run_root/render_large_text.log" 2>&1

# A scientifically meaningful mismatch must be packaged and reported rather
# than converted into an orchestration failure.  Preserve the verifier's exit
# code while allowing the immutable result bundle to be finalized.
set +e
"$python_bin" -B verify_random_threshold_reproduction.py \
  "$reference_output" \
  "$strict_output" \
  > "$run_root/reproduction_verification.log" 2>&1
verification_exit_code=$?
set -e
printf '%s\n' "$verification_exit_code" \
  > "$run_root/reproduction_verification.exit_code"

date -u +%Y-%m-%dT%H:%M:%SZ > "$run_root/pipeline_complete_utc.txt"
