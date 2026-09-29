#!/usr/bin/env bash
set -euo pipefail

bundle_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
workers="${1:-8}"
output_dir="${2:-results/ideal_capless_fixed_accuracy_scaling/reproduction_run}"
python_bin="${PYTHON_BIN:-python3}"

cd "$bundle_dir"
if [[ -e "$output_dir" ]]; then
  echo "Refusing to overwrite existing output: $output_dir" >&2
  exit 2
fi

export OPENBLAS_NUM_THREADS=1
export OMP_NUM_THREADS=1
export MKL_NUM_THREADS=1
export NUMEXPR_NUM_THREADS=1
export PYTHONPYCACHEPREFIX="${TMPDIR:-/tmp}/uen_forest_public_pycache"
export MPLCONFIGDIR="${TMPDIR:-/tmp}/uen_forest_public_mpl"

"$python_bin" -B random_per_run_threshold_search.py \
  --workers "$workers" \
  --threshold-scale 1e-7 \
  --output "$output_dir"

"$python_bin" -B report_ideal_strict_fixed_accuracy_1x4.py \
  --results "$output_dir"

"$python_bin" -B report_ideal_strict_fixed_accuracy_1x4.py \
  --large-text \
  --results "$output_dir"

"$python_bin" -B verify_random_threshold_reproduction.py \
  results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em10L0 \
  "$output_dir"
