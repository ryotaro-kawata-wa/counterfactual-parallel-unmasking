#!/usr/bin/env bash
set -euo pipefail

bundle_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
output_dir="${1:-results/ideal_capless_fixed_accuracy_scaling/smoke_run}"
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
export PYTHONPYCACHEPREFIX="${TMPDIR:-/tmp}/uen_forest_public_smoke_pycache"
export MPLCONFIGDIR="${TMPDIR:-/tmp}/uen_forest_public_smoke_mpl"

"$python_bin" -B random_per_run_threshold_search.py \
  --smoke \
  --workers 2 \
  --threshold-scale 1e-7 \
  --output "$output_dir"

"$python_bin" - "$output_dir" <<'PY'
import json
from pathlib import Path
import sys

output = Path(sys.argv[1])
status = json.loads((output / "status.json").read_text())
audit = json.loads((output / "audit.json").read_text())
if status.get("status") != "complete" or audit.get("status") != "pass":
    raise SystemExit("Smoke result did not complete and pass its audit.")
print(json.dumps({
    "status": status["status"],
    "audit": audit["status"],
    "per_run_searches": status["per_run_searches"],
    "seconds": status["seconds"],
}, indent=2))
PY
