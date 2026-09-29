#!/usr/bin/env python3
"""Please export the freshly built arXiv manuscript and only its active inputs.

Run through ``make arxiv-package`` so the recorder and bibliography are current.
The upload ZIP contains one main TeX file; provenance stays outside the upload.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import tempfile
import zipfile
from pathlib import Path


PAPER = Path(__file__).resolve().parents[1]
BUILD = PAPER / "build_arxiv"
ALLOWED = {".tex", ".pdf", ".png", ".jpg", ".jpeg", ".sty", ".cls", ".bst"}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=PAPER / "output/arxiv/arxiv_source.zip")
    args = parser.parse_args()
    output = args.output.resolve()
    recorder = BUILD / "main_arxiv.fls"
    baseline = PAPER / "output/pdf/arxiv_preprint.pdf"
    bbl = BUILD / "main_arxiv.bbl"
    for required in [recorder, baseline, bbl, BUILD / "main_arxiv.aux"]:
        if not required.is_file():
            raise SystemExit(f"Please run make arxiv first; missing {required}.")

    repo = Path(subprocess.check_output(
        ["git", "rev-parse", "--show-toplevel"], cwd=PAPER, text=True).strip())
    source_commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=PAPER, text=True).strip()
    used: set[Path] = set()
    for line in recorder.read_text().splitlines():
        if not line.startswith("INPUT "):
            continue
        path = (PAPER / line[6:]).resolve()
        if path.is_relative_to(PAPER):
            relative = path.relative_to(PAPER)
            if relative.parts[0] != "build_arxiv" and path.suffix in ALLOWED:
                used.add(path)
        elif path.is_relative_to(repo):
            raise SystemExit(f"Please localize this external project input: {path}")

    # Please obtain bibliography paths from the actual build, not a directory glob.
    auxiliary = (BUILD / "main_arxiv.aux").read_text()
    for group in re.findall(r"\\bibdata\{([^}]+)\}", auxiliary):
        for name in group.split(","):
            path = (PAPER / (name if name.endswith(".bib") else name + ".bib")).resolve()
            if not path.is_relative_to(PAPER) or not path.is_file():
                raise SystemExit(f"Please localize the bibliography: {path}")
            used.add(path)

    if not {PAPER / "main.tex", PAPER / "main_arxiv.tex"}.issubset(used):
        raise SystemExit("The recorder does not describe the expected arXiv entry point.")
    stale = [str(p.relative_to(PAPER)) for p in used
             if p.stat().st_mtime_ns > baseline.stat().st_mtime_ns]
    if stale:
        raise SystemExit("Please rebuild before packaging these changed inputs: "
                         + ", ".join(sorted(stale)))

    # Please use TeX Live's standard natbib instead of redistributing the old
    # conference-bundled copy. The isolated build checks its rendered equivalence.
    omitted = []
    if PAPER / "natbib.sty" in used:
        used.remove(PAPER / "natbib.sty")
        omitted.append({"file": "natbib.sty",
                        "reason": "Use the standard natbib distributed with TeX Live."})

    payload: dict[str, bytes] = {}
    origin: dict[str, str | None] = {}
    source_hashes = {str(p.relative_to(PAPER)): sha256(p.read_bytes())
                     for p in sorted(used)}
    for path in sorted(used):
        relative = path.relative_to(PAPER).as_posix()
        if relative == "main_arxiv.tex":
            continue
        payload[relative] = path.read_bytes()
        origin[relative] = relative

    # Please inline only the entry-point wrapper; the shared manuscript stays intact.
    wrapper = (PAPER / "main_arxiv.tex").read_text().splitlines()
    active = [line for line in wrapper if line.strip() and not line.lstrip().startswith("%")]
    if active.count(r"\input{main.tex}") != 1:
        raise SystemExit("Please review the changed arXiv wrapper before exporting.")
    prefix = "\n".join(line for line in active if line != r"\input{main.tex}") + "\n"
    payload["main.tex"] = prefix.encode() + payload["main.tex"]

    # Please avoid a PDF and an included TeX file sharing a stem: upload cleanup
    # may otherwise mistake an included figure for a generated document output.
    renamed = {}
    for name in list(payload):
        path = Path(name)
        if path.suffix == ".pdf" and path.with_suffix(".tex").as_posix() in payload:
            destination = path.with_name(path.stem + "_artwork.pdf").as_posix()
            if destination in payload:
                raise SystemExit(f"Conflicting figure destination: {destination}")
            renamed[name] = destination
            payload[destination] = payload.pop(name)
            origin[destination] = origin.pop(name)
    for name, content in list(payload.items()):
        if name.endswith(".tex"):
            for old, new in renamed.items():
                content = content.replace(old.encode(), new.encode())
            payload[name] = content

    payload["main.bbl"] = bbl.read_bytes()
    origin["main.bbl"] = "build_arxiv/main_arxiv.bbl"
    configuration = {
        "spec_version": 1,
        "process": {"compiler": "pdflatex"},
        "sources": [
            {"filename": "main.tex", "usage": "toplevel"},
            *[{"filename": name, "usage": "include"}
              for name in sorted(payload) if name.endswith(".tex") and name != "main.tex"],
        ],
    }
    payload["00README.json"] = (json.dumps(configuration, indent=2) + "\n").encode()
    origin["00README.json"] = None

    for name in payload:
        if any(part.startswith(".") or not re.fullmatch(r"[A-Za-z0-9_+.,=\-]+", part)
               for part in Path(name).parts):
            raise SystemExit(f"Please use an arXiv-compatible filename: {name}")
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="arxiv-export-", dir=output.parent) as temporary:
        temporary_zip = Path(temporary) / "source.zip"
        with zipfile.ZipFile(temporary_zip, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
            for name, content in sorted(payload.items()):
                entry = zipfile.ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
                entry.compress_type = zipfile.ZIP_DEFLATED
                entry.create_system = 3
                entry.external_attr = 0o100644 << 16
                archive.writestr(entry, content, compresslevel=9)
        temporary_zip.replace(output)

    manifest = {
        "source_commit": source_commit,
        "manuscript_directory": str(PAPER.relative_to(repo)),
        "archive": output.name,
        "archive_sha256": sha256(output.read_bytes()),
        "archive_bytes": output.stat().st_size,
        "entrypoint": "main.tex",
        "compiler": "pdflatex",
        "reference_pdf_sha256": sha256(baseline.read_bytes()),
        "source_input_sha256": source_hashes,
        "omitted_standard_packages": omitted,
        "figure_renames": renamed,
        "files": [{"path": name, "bytes": len(content), "sha256": sha256(content),
                   "source": origin[name]}
                  for name, content in sorted(payload.items())],
        "scope": "Current manuscript sources only; no experiment/Lean code, reviews, logs or generated full-paper PDF.",
    }
    manifest_path = output.with_name(output.stem + "_manifest.json")
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Source ZIP: {output}")
    print(f"Packaged {len(payload)} files ({output.stat().st_size:,} bytes); entry point: main.tex")
    print(f"Provenance: {manifest_path}")


if __name__ == "__main__":
    main()
