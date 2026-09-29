"""Package and index one immutable four-forest reproduction run."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import shutil


RUN_ID = "20260925T114740Z__git-3eda55e59630"
GIT_COMMIT = "3eda55e596301a179d9a55471032cd28b84c3366"
SOURCE_ARCHIVE_SHA256 = (
    "540028feea661aab15c127eed7752fc558fe30f43fddb31c760d1057c5f1f97b"
)
PRECURSOR_ARCHIVE_SHA256 = (
    "0ae138a50a4930c7ae3301a16efbb1eda295744f59c0fba6a3088fbb4b0041dd"
)
ORCHESTRATOR_SHA256 = (
    "2171ddc3a853e607a599e294ae40b427de5b6faa0a3b651e12b31490c93444c0"
)
POSTPROCESS_WATCHER_SHA256 = (
    "3a38e2b38ebfd39d4e79afbed289f01173b163ac1348b9c92bfe29e847e7f3ab"
)
RECOVERY_FINALIZER_SHA256 = (
    "5a044d06779d02c59dc11d28b6b9847492907943b2bca4a731e03f76a1b0aaf6"
)

RUN_ROOT = Path("/home/kawata/work/uen_forest_toy_fresh_reruns") / RUN_ID
BUNDLE = (
    RUN_ROOT
    / "source/experiments/forest_toy/public_release/ideal_strict_fixed_accuracy_k1em10L0"
)
PARENT = BUNDLE / "results/ideal_capless_fixed_accuracy_scaling"
STRICT = RUN_ROOT / "strict_random"
REFERENCE = (
    RUN_ROOT
    / "bundled_reference_results/random_per_run_threshold_search_k1em10L0"
)
NAMED = RUN_ROOT / "named_figures"
SHARE = RUN_ROOT / "share"


def load_json(path: Path):
    return json.loads(path.read_text())


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            value.update(block)
    return value.hexdigest()


def copy_audit_tree(source: Path, destination: Path) -> None:
    """Copy auditable outputs while excluding bulky caches and lock files."""
    for path in sorted(source.rglob("*")):
        relative = path.relative_to(source)
        if "artifacts" in relative.parts or path.name == "runner.lock":
            continue
        target = destination / relative
        if path.is_dir():
            target.mkdir(parents=True, exist_ok=True)
        elif path.is_file():
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(path, target)


def main() -> None:
    if not (RUN_ROOT / "pipeline_complete_utc.txt").exists():
        raise SystemExit("The experiment pipeline has not completed.")

    parent_status = load_json(PARENT / "status.json")
    strict_status = load_json(STRICT / "status.json")
    parent_audit = load_json(PARENT / "audit.json")
    strict_audit = load_json(STRICT / "audit.json")
    comparison = load_json(STRICT / "reproduction_comparison.json")
    if parent_status.get("status") != "complete":
        raise SystemExit(f"Parent status is not complete: {parent_status}")
    if strict_status.get("status") != "complete":
        raise SystemExit(f"Strict status is not complete: {strict_status}")

    figure_data_hash = digest(STRICT / "figure_data.json")
    tag = f"{RUN_ID}__data-{figure_data_hash[:12]}"
    NAMED.mkdir(parents=True, exist_ok=False)
    artifact_records = []
    stems = (
        "ideal_strict_fixed_accuracy_linear_errorbars_1x4",
        "ideal_strict_fixed_accuracy_linear_errorbars_1x4_large_text",
    )
    for stem in stems:
        for suffix in (".png", ".pdf", ".json"):
            source = STRICT / f"{stem}{suffix}"
            destination = NAMED / f"{stem}__{tag}{suffix}"
            shutil.copy2(source, destination)
            artifact_records.append(
                {
                    "path": str(destination.relative_to(RUN_ROOT)),
                    "sha256": digest(destination),
                    "bytes": destination.stat().st_size,
                }
            )

    manifest = {
        "run_id": RUN_ID,
        "status": "verified" if comparison.get("status") == "pass" else "completed_with_difference",
        "canonical": False,
        "node": load_json(STRICT / "environment.json").get("hostname"),
        "workers": 8,
        "source_git_commit": GIT_COMMIT,
        "source_archive_sha256": SOURCE_ARCHIVE_SHA256,
        "precursor_archive_sha256": PRECURSOR_ARCHIVE_SHA256,
        "orchestrator_sha256": ORCHESTRATOR_SHA256,
        "postprocess_watcher_sha256": POSTPROCESS_WATCHER_SHA256,
        "recovery_finalizer_sha256": RECOVERY_FINALIZER_SHA256,
        "postprocessor_live_sha256": digest(RUN_ROOT / "postprocess.py"),
        "source_manifest_sha256": digest(BUNDLE / "SOURCE_MANIFEST.json"),
        "parent_design_sha256": digest(PARENT / "design.json"),
        "strict_design_sha256": digest(STRICT / "design.json"),
        "figure_data_sha256": figure_data_hash,
        "started_utc": parent_status.get("started_utc"),
        "pipeline_completed_utc": (RUN_ROOT / "pipeline_complete_utc.txt").read_text().strip(),
        "parent_seconds": parent_status.get("seconds"),
        "strict_random_seconds": strict_status.get("seconds"),
        "freshness": {
            "proposal_observations_recomputed": True,
            "proposal_tuning_recomputed": True,
            "proposal_confirmation_recomputed": True,
            "random_observations_recomputed": True,
            "strict_random_seed_records": None,
            "strict_random_reused_budget_records": strict_status.get("reused_budget_records"),
            "fixed_precursors_are_hashed_design_inputs": True,
        },
        "parent_audit_status": parent_audit.get("status"),
        "strict_audit_status": strict_audit.get("status"),
        "reference_comparison": comparison,
        "reference_verifier_exit_code": int(
            (RUN_ROOT / "reproduction_verification.exit_code").read_text().strip()
        ),
        "render_recovery": {
            "needed": True,
            "reason": (
                "The frozen renderer wrote PNG/PDF but rejected an external "
                "result path while creating relative-path metadata."
            ),
            "numerical_outputs_modified": False,
            "method": (
                "Copy the completed strict output into a bundle-local render "
                "workspace, render there without changing source, then copy "
                "only the six standard/large-text figure artifacts back."
            ),
        },
        "reference_figure_data_sha256": digest(REFERENCE / "figure_data.json"),
        "artifacts": artifact_records,
        "excluded_from_share": [
            "regenerable per-job artifacts/ directories",
            "runner.lock files",
            "Python and Matplotlib caches",
        ],
    }
    manifest_path = RUN_ROOT / "RUN_MANIFEST.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n")

    large_pdf = next(
        row["path"]
        for row in artifact_records
        if "large_text" in row["path"] and row["path"].endswith(".pdf")
    )
    large_png = next(
        row["path"]
        for row in artifact_records
        if "large_text" in row["path"] and row["path"].endswith(".png")
    )
    readme = f"""# Four-forest ideal fresh reproduction

- Run ID: `{RUN_ID}`
- Source commit: `{GIT_COMMIT}`
- Node: `{manifest['node']}` with 8 workers
- Existing records reused: none for Proposal or Random observations
- Fixed precursor files: hashed design inputs only
- Reference comparison: `{comparison.get('status')}`
- Canonical paper result replaced: no

## Paper artifacts

- Large-text PDF: `{large_pdf}`
- Large-text PNG: `{large_png}`
- Figure-data SHA-256: `{figure_data_hash}`

`RUN_MANIFEST.json` contains the full hashes, timings, audits, comparison, and
artifact inventory.  The `share/` directory omits only regenerable per-job
cache artifacts and lock files; the raw JSON/JSONL records and source snapshots
needed for inspection are retained.
"""
    (RUN_ROOT / "README.md").write_text(readme)

    (SHARE / "named_figures").mkdir(parents=True, exist_ok=False)
    for path in NAMED.iterdir():
        shutil.copy2(path, SHARE / "named_figures" / path.name)
    copy_audit_tree(PARENT, SHARE / "parent_fresh")
    copy_audit_tree(STRICT, SHARE / "strict_random_fresh")
    if (RUN_ROOT / "incidents").exists():
        copy_audit_tree(RUN_ROOT / "incidents", SHARE / "incidents")
    for name in (
        "README.md",
        "RUN_MANIFEST.json",
        "source_checksum_check.log",
        "source_checksum_check_ignore_exported_logs.log",
        "full_parent.log",
        "strict_random.log",
        "render_standard.log",
        "render_large_text.log",
        "render_standard_recovery.log",
        "render_large_text_recovery.log",
        "reproduction_verification.log",
        "reproduction_verification.exit_code",
        "pipeline_complete_utc.txt",
        "orchestrator.sh",
        "recovery_finalize.sh",
    ):
        source = RUN_ROOT / name
        if source.exists():
            shutil.copy2(source, SHARE / name)

    index_path = RUN_ROOT.parent / "RUN_INDEX.json"
    index = load_json(index_path) if index_path.exists() else {"runs": []}
    if any(row.get("run_id") == RUN_ID for row in index["runs"]):
        raise SystemExit(f"Run already indexed: {RUN_ID}")
    index["runs"].append(
        {
            "run_id": RUN_ID,
            "status": manifest["status"],
            "canonical": False,
            "relative_directory": RUN_ID,
            "source_git_commit": GIT_COMMIT,
            "figure_data_sha256": figure_data_hash,
            "manifest_sha256": digest(manifest_path),
        }
    )
    index_path.write_text(json.dumps(index, indent=2, ensure_ascii=False) + "\n")


if __name__ == "__main__":
    main()
