#!/usr/bin/env bash
set -euo pipefail

bundle_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
python_bin="${PYTHON_BIN:-python3}"
result_root="results/ideal_capless_fixed_accuracy_scaling"

cd "$bundle_dir"
"$python_bin" -B verify_random_threshold_reproduction.py \
  "$result_root/random_per_run_threshold_search_k1em10L0" \
  "$result_root/random_per_run_threshold_search_k1em10L0_fresh"
