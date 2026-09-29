"""Compare an accumulated threshold search with a fresh-from-scratch rerun.

The comparison focuses on the estimand used by the paper: the selected
per-run budgets and their cellwise query summaries.  It additionally checks
all shared KL observations up to explicit floating-point tolerances.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path


def load_json(path):
    return json.loads(Path(path).read_text())


def digest(path):
    value = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            value.update(block)
    return value.hexdigest()


def selection_key(row):
    return (
        row["target"],
        int(row["n"]),
        int(row["data_repeat"]),
        int(row["algorithm_repeat"]),
    )


def record_key(row):
    return selection_key(row) + (int(row["budget"]),)


def cell_key(row):
    return row["target"], int(row["n"])


def numeric_difference(left, right):
    """Return an absolute difference while handling paired null values."""
    if left is None or right is None:
        return 0.0 if left == right else math.inf
    return abs(float(left) - float(right))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("reference", type=Path)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--relative-tolerance", type=float, default=1e-12)
    parser.add_argument("--absolute-tolerance", type=float, default=1e-18)
    args = parser.parse_args()

    reference = args.reference.resolve()
    candidate = args.candidate.resolve()
    output = (
        args.output.resolve()
        if args.output is not None
        else candidate / "reproduction_comparison.json"
    )
    errors = []

    reference_design = load_json(reference / "design.json")
    candidate_design = load_json(candidate / "design.json")
    reference_audit = load_json(reference / "audit.json")
    candidate_audit = load_json(candidate / "audit.json")
    reference_status = load_json(reference / "status.json")
    candidate_status = load_json(candidate / "status.json")

    if reference_status.get("status") != "complete":
        errors.append("reference status is not complete")
    if candidate_status.get("status") != "complete":
        errors.append("candidate status is not complete")
    if reference_audit.get("status") != "pass":
        errors.append("reference audit did not pass")
    if candidate_audit.get("status") != "pass":
        errors.append("candidate audit did not pass")

    threshold_match = (
        reference_design.get("relative_L0_factor")
        == candidate_design.get("relative_L0_factor")
        and reference_design.get("thresholds") == candidate_design.get("thresholds")
    )
    if not threshold_match:
        errors.append("threshold definitions differ")

    source_hash_match = (
        reference_audit.get("source_sha256")
        == candidate_audit.get("source_sha256")
    )
    if not source_hash_match:
        errors.append("source hashes differ")

    # A seeded reference has one additional input hash.  Compare every input
    # shared by the two designs and report the seed-record distinction later.
    reference_inputs = reference_audit.get("input_sha256", {})
    candidate_inputs = candidate_audit.get("input_sha256", {})
    common_input_names = sorted(set(reference_inputs) & set(candidate_inputs))
    input_hash_mismatches = [
        name
        for name in common_input_names
        if reference_inputs[name] != candidate_inputs[name]
    ]
    if input_hash_mismatches:
        errors.append("shared input hashes differ")

    reference_selections = {
        selection_key(row): row for row in load_json(reference / "selections.json")
    }
    candidate_selections = {
        selection_key(row): row for row in load_json(candidate / "selections.json")
    }
    selection_identity_match = set(reference_selections) == set(candidate_selections)
    if not selection_identity_match:
        errors.append("selection identities differ")

    selection_fields = (
        "budget",
        "lower_observed_budget",
        "bracket_width",
        "success",
    )
    selection_mismatches = []
    selected_kl_max_absolute_difference = {"K": 0.0, "K_upper": 0.0}
    selected_kl_not_close = {"K": 0, "K_upper": 0}
    for key in sorted(set(reference_selections) & set(candidate_selections)):
        left, right = reference_selections[key], candidate_selections[key]
        for field in selection_fields:
            if left[field] != right[field]:
                selection_mismatches.append({
                    "identity": list(key),
                    "field": field,
                    "reference": left[field],
                    "candidate": right[field],
                })
        for field in ("K", "K_upper"):
            difference = numeric_difference(left[field], right[field])
            selected_kl_max_absolute_difference[field] = max(
                selected_kl_max_absolute_difference[field], difference
            )
            if not math.isclose(
                float(left[field]),
                float(right[field]),
                rel_tol=args.relative_tolerance,
                abs_tol=args.absolute_tolerance,
            ):
                selected_kl_not_close[field] += 1
    if selection_mismatches:
        errors.append("selected budgets or brackets differ")
    if any(selected_kl_not_close.values()):
        errors.append("selected KL values exceed the numerical tolerance")

    reference_summary = {
        cell_key(row): row for row in load_json(reference / "random_summary.json")
    }
    candidate_summary = {
        cell_key(row): row for row in load_json(candidate / "random_summary.json")
    }
    summary_fields = ("Q", "Q_min", "Q_max", "Q_values", "successes", "confirmed")
    summary_mismatches = []
    if set(reference_summary) != set(candidate_summary):
        errors.append("summary cell identities differ")
    for key in sorted(set(reference_summary) & set(candidate_summary)):
        left, right = reference_summary[key], candidate_summary[key]
        for field in summary_fields:
            if left[field] != right[field]:
                summary_mismatches.append({
                    "cell": list(key),
                    "field": field,
                    "reference": left[field],
                    "candidate": right[field],
                })
    if summary_mismatches:
        errors.append("paper-facing random query summaries differ")

    reference_records = {
        record_key(row): row for row in load_json(reference / "records.json")
    }
    candidate_records = {
        record_key(row): row for row in load_json(candidate / "records.json")
    }
    shared_record_keys = sorted(set(reference_records) & set(candidate_records))
    record_success_mismatches = 0
    record_kl_max_absolute_difference = {"K": 0.0, "K_upper": 0.0}
    record_kl_not_close = {"K": 0, "K_upper": 0}
    for key in shared_record_keys:
        left, right = reference_records[key], candidate_records[key]
        if left["success"] != right["success"]:
            record_success_mismatches += 1
        for field in ("K", "K_upper"):
            difference = numeric_difference(left[field], right[field])
            record_kl_max_absolute_difference[field] = max(
                record_kl_max_absolute_difference[field], difference
            )
            if left[field] is None or right[field] is None:
                close = left[field] == right[field]
            else:
                close = math.isclose(
                    float(left[field]),
                    float(right[field]),
                    rel_tol=args.relative_tolerance,
                    abs_tol=args.absolute_tolerance,
                )
            if not close:
                record_kl_not_close[field] += 1
    if record_success_mismatches:
        errors.append("shared record success labels differ")
    if any(record_kl_not_close.values()):
        errors.append("shared record KL values exceed the numerical tolerance")

    reference_figure = load_json(reference / "figure_data.json")
    candidate_figure = load_json(candidate / "figure_data.json")
    proposal_exact_match = reference_figure["proposal"] == candidate_figure["proposal"]
    if not proposal_exact_match:
        errors.append("proposal figure data differ")

    report = {
        "status": "pass" if not errors else "fail",
        # Store portable sibling names rather than machine-specific absolute
        # paths.  The design hashes below still identify the inputs exactly.
        "reference": reference.name,
        "candidate": candidate.name,
        "reference_design_sha256": digest(reference / "design.json"),
        "candidate_design_sha256": digest(candidate / "design.json"),
        "relative_L0_factor": candidate_design.get("relative_L0_factor"),
        "candidate_reused_budget_records": candidate_audit.get(
            "reused_budget_records"
        ),
        "threshold_match": threshold_match,
        "source_hash_match": source_hash_match,
        "shared_input_hash_mismatches": input_hash_mismatches,
        "selection_identity_match": selection_identity_match,
        "selection_count": len(candidate_selections),
        "selection_mismatch_count": len(selection_mismatches),
        "selection_mismatch_examples": selection_mismatches[:10],
        "selected_kl_max_absolute_difference": selected_kl_max_absolute_difference,
        "selected_kl_not_close": selected_kl_not_close,
        "summary_cell_count": len(candidate_summary),
        "summary_mismatch_count": len(summary_mismatches),
        "summary_mismatch_examples": summary_mismatches[:10],
        "proposal_figure_data_exact_match": proposal_exact_match,
        "reference_record_count": len(reference_records),
        "candidate_record_count": len(candidate_records),
        "shared_record_count": len(shared_record_keys),
        "candidate_records_subset_of_reference": (
            set(candidate_records) <= set(reference_records)
        ),
        "shared_record_success_mismatch_count": record_success_mismatches,
        "shared_record_kl_max_absolute_difference": (
            record_kl_max_absolute_difference
        ),
        "shared_record_kl_not_close": record_kl_not_close,
        "relative_tolerance": args.relative_tolerance,
        "absolute_tolerance": args.absolute_tolerance,
        "errors": errors,
    }
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps(report, indent=2, ensure_ascii=False))
    if errors:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
