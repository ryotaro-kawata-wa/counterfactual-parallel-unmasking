#!/usr/bin/env bash
set -euo pipefail

# Recover only the paper-rendering and packaging steps.  The completed parent
# and strict-random numerical outputs are treated as immutable inputs.
run_root="/home/kawata/work/uen_forest_toy_fresh_reruns/20260925T114740Z__git-3eda55e59630"
bundle="$run_root/source/experiments/forest_toy/public_release/ideal_strict_fixed_accuracy_k1em10L0"
python_bin="/home/kawata/work/uen_forest_toy_robustness_20260919/.venv/bin/python"
strict_output="$run_root/strict_random"
render_workspace="$bundle/results/render_workspace_20260925T114740Z__git-3eda55e59630"
reference_output="$run_root/bundled_reference_results/random_per_run_threshold_search_k1em10L0"

export OPENBLAS_NUM_THREADS=1
export OMP_NUM_THREADS=1
export MKL_NUM_THREADS=1
export NUMEXPR_NUM_THREADS=1
export PYTHONUNBUFFERED=1
export PYTHONPYCACHEPREFIX=/tmp/uen_4forest_20260925_pycache
export MPLCONFIGDIR=/tmp/uen_4forest_20260925_mpl

mkdir -p "$run_root/incidents"
if [[ -f "$run_root/pipeline_failed.txt" ]]; then
  mv "$run_root/pipeline_failed.txt" \
    "$run_root/incidents/initial_renderer_path_failure.txt"
fi
if [[ -f "$run_root/postprocess_not_run.txt" ]]; then
  mv "$run_root/postprocess_not_run.txt" \
    "$run_root/incidents/initial_postprocess_not_run.txt"
fi

test ! -e "$render_workspace"
cp -a "$strict_output" "$render_workspace"
rm -f "$render_workspace/runner.lock"

cd "$bundle"
"$python_bin" -B report_ideal_strict_fixed_accuracy_1x4.py \
  --results "$render_workspace" \
  > "$run_root/render_standard_recovery.log" 2>&1
"$python_bin" -B report_ideal_strict_fixed_accuracy_1x4.py \
  --large-text \
  --results "$render_workspace" \
  > "$run_root/render_large_text_recovery.log" 2>&1

for stem in \
  ideal_strict_fixed_accuracy_linear_errorbars_1x4 \
  ideal_strict_fixed_accuracy_linear_errorbars_1x4_large_text; do
  for suffix in png pdf json; do
    cp "$render_workspace/${stem}.${suffix}" "$strict_output/${stem}.${suffix}"
  done
done

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
"$python_bin" -B "$run_root/postprocess.py" \
  > "$run_root/postprocess.log" 2>&1
