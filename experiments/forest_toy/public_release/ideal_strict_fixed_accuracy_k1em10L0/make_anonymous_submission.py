"""Build an anonymized, self-contained submission archive.

The scientific source bundle remains unchanged.  This exporter creates a
separate directory containing the experiment code, portable result records,
and paper figures, while omitting machine-level provenance that is unsuitable
for double-blind review.
"""

from __future__ import annotations

import argparse
import getpass
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import socket
import stat
import tarfile
import tempfile
import zipfile


SOURCE_ROOT = Path(__file__).resolve().parent

# These files document the private provenance bundle or implement this export.
# They are useful in the working repository but should not be included in the
# double-blind artifact itself.
EXCLUDED_TOP_LEVEL = {
    "ANONYMIZATION.md",
    "SHA256SUMS",
    "SOURCE_MANIFEST.json",
    "make_anonymous_submission.py",
    "reruns",
}
EXCLUDED_DIRECTORY_NAMES = {
    ".git",
    "__pycache__",
    "artifacts",
    "target_profiles",
}
EXCLUDED_FILE_NAMES = {
    ".DS_Store",
    "environment.json",
    "execution_history.json",
    "runner.lock",
}
EXCLUDED_SUFFIXES = {
    ".dylib",
    ".log",
    ".o",
    ".pyc",
    ".so",
}
TEXT_SUFFIXES = {
    ".bib",
    ".c",
    ".cfg",
    ".csv",
    ".h",
    ".json",
    ".jsonl",
    ".md",
    ".py",
    ".sh",
    ".tex",
    ".toml",
    ".txt",
    ".yaml",
    ".yml",
}
SOURCE_SUFFIXES = {".c", ".h", ".py", ".sh"}

# Use escaped code points so the exporter itself contains no Japanese text.
# The supplementary artifact does not include this local export utility.
JAPANESE_PATTERN = re.compile(
    "[\u2e80-\u30ff\u3400-\u9fff\uf900-\ufaff\uff00-\uffef"
    "\U00020000-\U0002fa1f]+"
)

# Explicitly requested identity tokens are encoded rather than written into
# the exporter source.  They are always redacted and always included in the
# final hard-fail scan, independent of the account running the exporter.
ALWAYS_FORBIDDEN_TOKENS = {
    bytes.fromhex(value).decode("ascii")
    for value in (
        "72796f7461726f",
        "6b6177617461",
        "686179616b617761",
        "7361746f736869",
        "7461696a69",
        "73757a756b69",
    )
}


def sha256(path: Path) -> str:
    """Return a streaming SHA-256 digest for one file."""
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def is_relative_to(path: Path, parent: Path) -> bool:
    """Provide Path.is_relative_to behavior with an explicit compatibility shim."""
    try:
        path.relative_to(parent)
    except ValueError:
        return False
    return True


def include_file(relative: Path) -> bool:
    """Apply the conservative allowlist policy for the submission bundle."""
    if relative.parts[0] in EXCLUDED_TOP_LEVEL:
        return False
    if any(part in EXCLUDED_DIRECTORY_NAMES for part in relative.parts[:-1]):
        return False
    if relative.name in EXCLUDED_FILE_NAMES:
        return False
    if relative.suffix.lower() in EXCLUDED_SUFFIXES:
        return False
    return True


def replacement_rules(extra_tokens: list[str]):
    """Construct ordered redaction rules without recording local paths."""
    rules = [
        (
            "japanese_text",
            JAPANESE_PATTERN,
            "REDACTED",
        ),
        (
            "unix_home",
            re.compile(r"/(?:Users|home)/[^/\s\"'<>]+"),
            "<HOME>",
        ),
        (
            "windows_home",
            re.compile(r"[A-Za-z]:\\\\Users\\\\[^\\\\\s\"'<>]+"),
            "<HOME>",
        ),
        (
            "local_hostname",
            re.compile(r"\b[A-Za-z0-9][A-Za-z0-9._-]*\.local\b", re.IGNORECASE),
            "local-workstation",
        ),
        (
            "cluster_hostname",
            re.compile(r"\bnewton(?:_proxy|\d+)\b", re.IGNORECASE),
            "compute-node",
        ),
        (
            "email",
            re.compile(
                r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}\b"
            ),
            "<REDACTED_EMAIL>",
        ),
        (
            "repository_url",
            re.compile(
                r"https?://(?:www\.)?(?:github|gitlab)\.com/[^\s\"'<>]+",
                re.IGNORECASE,
            ),
            "https://example.invalid/anonymous/repository",
        ),
    ]
    dynamic_tokens = ALWAYS_FORBIDDEN_TOKENS | {
        token.strip()
        for token in [getpass.getuser(), Path.home().name, socket.gethostname()]
        + extra_tokens
        if token.strip()
    }
    for index, token in enumerate(sorted(dynamic_tokens, key=len, reverse=True)):
        rules.append(
            (
                f"explicit_token_{index}",
                re.compile(re.escape(token), re.IGNORECASE),
                "anonymous",
            )
        )
    return rules, dynamic_tokens


def sanitize_text(text: str, rules, counts: dict[str, int]) -> str:
    """Apply all redactions and record how often each rule was used."""
    for label, pattern, replacement in rules:
        text, replacements = pattern.subn(replacement, text)
        counts[label] = counts.get(label, 0) + replacements
    return text


def sanitize_relative_path(
    relative: Path,
    rules,
    counts: dict[str, int],
) -> Path:
    """Sanitize every filename component using filesystem-safe placeholders."""
    parts = []
    for component in relative.parts:
        sanitized = component
        for label, pattern, _replacement in rules:
            sanitized, replacements = pattern.subn("redacted", sanitized)
            if replacements:
                key = f"path_{label}"
                counts[key] = counts.get(key, 0) + replacements
        parts.append(sanitized)
    return Path(*parts)


def copy_submission_files(
    destination_root: Path,
    rules,
    counts: dict[str, int],
) -> tuple[int, int, list[str]]:
    """Copy allowed files, sanitizing every recognized text format."""
    copied = 0
    sanitized_text_files = 0
    excluded_categories: set[str] = set()
    destinations: set[Path] = set()
    for source in sorted(SOURCE_ROOT.rglob("*")):
        if not source.is_file():
            continue
        relative = source.relative_to(SOURCE_ROOT)
        if not include_file(relative):
            if relative.parts[0] == "reruns":
                excluded_categories.add("full machine-level rerun provenance")
            elif source.suffix.lower() == ".log":
                excluded_categories.add("machine logs")
            elif source.name in {"environment.json", "execution_history.json"}:
                excluded_categories.add("machine environment and timing records")
            elif relative.parts[0] in {"ANONYMIZATION.md", "make_anonymous_submission.py"}:
                excluded_categories.add("local export tooling")
            else:
                excluded_categories.add("regenerable caches and private manifests")
            continue

        destination_relative = sanitize_relative_path(relative, rules, counts)
        if destination_relative in destinations:
            suffix = hashlib.sha256(str(relative).encode("utf-8")).hexdigest()[:8]
            destination_relative = destination_relative.with_name(
                f"{destination_relative.stem}__{suffix}{destination_relative.suffix}"
            )
        if destination_relative in destinations:
            raise RuntimeError(f"Anonymized path collision: {destination_relative}")
        destinations.add(destination_relative)
        destination = destination_root / destination_relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        if source.suffix.lower() in TEXT_SUFFIXES or source.name == "requirements.txt":
            original = source.read_text(encoding="utf-8")
            sanitized = sanitize_text(original, rules, counts)
            if source.suffix.lower() == ".json":
                # Refuse to emit malformed machine-readable artifacts.
                json.loads(sanitized)
            destination.write_text(sanitized, encoding="utf-8")
            sanitized_text_files += 1
        else:
            shutil.copyfile(source, destination)
        # Normalize permissions so a restrictive source umask cannot make the
        # submitted code unreadable.  Preserve only whether a file is meant to
        # be executable; ordinary source and data files are world-readable.
        source_is_executable = bool(source.stat().st_mode & 0o111)
        destination.chmod(0o755 if source_is_executable else 0o644)
        copied += 1
    return copied, sanitized_text_files, sorted(excluded_categories)


def write_submission_readme(destination_root: Path) -> None:
    """Explain what the anonymized artifact contains and how to verify it."""
    content = """# Anonymous supplementary-code artifact

This directory was generated for double-blind review.  It contains the
experiment source, portable result records, and paper-facing figures.  Git
history, absolute user paths, hostnames, machine logs, environment records,
Japanese prose, and the full machine-level rerun provenance were intentionally
excluded or redacted.  Scientific arrays and reported numerical values were
not altered.

Placeholders such as `<HOME>`, `compute-node`, and `REDACTED` may appear in
source or historical JSON metadata.  They are presentation-only redactions
and are not runtime inputs.

Verify the artifact after extraction with:

```bash
shasum -a 256 -c SHA256SUMS
```

The main fresh reproduction can be launched with eight workers using:

```bash
./reproduce_fresh.sh 8
```

See `ANONYMIZATION_REPORT.json` for the exact export policy.
"""
    (destination_root / "ANONYMIZED_README.md").write_text(
        content, encoding="utf-8"
    )


def write_source_manifest(destination_root: Path) -> None:
    """Describe the anonymized source itself rather than private-source hashes."""
    files = []
    for path in sorted(destination_root.rglob("*")):
        if not path.is_file():
            continue
        if path.suffix.lower() not in SOURCE_SUFFIXES and path.name != "requirements.txt":
            continue
        files.append(
            {
                "path": str(path.relative_to(destination_root)),
                "sha256": sha256(path),
            }
        )
    manifest = {
        "schema_version": 1,
        "kind": "anonymized submission source manifest",
        "source_files": files,
        "transformations": [
            "identity-bearing paths, hosts, emails, and repository URLs redacted",
            "Japanese text runs replaced with REDACTED",
            "numerical arrays and reported numerical values unchanged",
        ],
    }
    (destination_root / "SOURCE_MANIFEST.json").write_text(
        json.dumps(manifest, indent=2, ensure_ascii=True) + "\n",
        encoding="utf-8",
    )


def forbidden_findings(root: Path, dynamic_tokens: set[str]) -> list[dict[str, str]]:
    """Scan filenames and file bytes for common double-blind leaks."""
    token_patterns = [
        token.encode("utf-8").lower()
        for token in dynamic_tokens
        if len(token) >= 3
    ]
    byte_patterns = [
        ("absolute Unix home", re.compile(rb"/(?:users|home)/", re.IGNORECASE)),
        ("absolute Windows home", re.compile(rb"[a-z]:\\\\users\\\\", re.IGNORECASE)),
        ("local hostname", re.compile(rb"[a-z0-9._-]+\.local\b", re.IGNORECASE)),
        ("cluster hostname", re.compile(rb"\bnewton(?:_proxy|\d+)\b", re.IGNORECASE)),
        ("repository URL", re.compile(rb"(?:github|gitlab)\.com/", re.IGNORECASE)),
        ("Git-labelled commit", re.compile(rb"\bgit-[0-9a-f]{7,40}\b", re.IGNORECASE)),
        ("source commit field", re.compile(rb"\"source_commit\"", re.IGNORECASE)),
    ]
    findings: list[dict[str, str]] = []
    for path in sorted(root.rglob("*")):
        relative = path.relative_to(root)
        relative_lower = str(relative).lower().encode("utf-8")
        for token in token_patterns:
            if token in relative_lower:
                findings.append({"path": str(relative), "reason": "explicit token in path"})
        if not path.is_file():
            continue
        payload = path.read_bytes()
        payload_lower = payload.lower()
        if path.suffix.lower() in TEXT_SUFFIXES or path.name == "requirements.txt":
            decoded = payload.decode("utf-8")
            if JAPANESE_PATTERN.search(decoded):
                findings.append({"path": str(relative), "reason": "Japanese text"})
        for token in token_patterns:
            if token in payload_lower:
                findings.append({"path": str(relative), "reason": "explicit token"})
        for label, pattern in byte_patterns:
            if pattern.search(payload):
                findings.append({"path": str(relative), "reason": label})
    return findings


def write_report(
    destination_root: Path,
    copied: int,
    sanitized_text_files: int,
    counts: dict[str, int],
    excluded_categories: list[str],
) -> None:
    """Write a portable report containing no source-machine identifiers."""
    report = {
        "schema_version": 1,
        "artifact": "ideal forest fixed-accuracy supplementary code",
        "copied_source_files": copied,
        "sanitized_text_files": sanitized_text_files,
        "replacement_counts": {
            key: value for key, value in sorted(counts.items()) if value
        },
        "excluded_categories": excluded_categories,
        "scientific_arrays_modified": False,
        "reported_numerical_values_modified": False,
        "japanese_text_policy": "replace each contiguous run with REDACTED",
        "requested_personal_tokens_policy": "always redact and hard-fail scan",
        "git_history_included": False,
        "archive_identity_metadata": {
            "tar_gzip": {
                "uid": 0,
                "gid": 0,
                "uname": "anonymous",
                "gname": "anonymous",
                "mtime": 0,
            },
            "zip": {
                "timestamp": "1980-01-01T00:00:00",
                "archive_comment_bytes": 0,
                "absolute_paths": False,
            },
        },
        "validation": "pending",
    }
    (destination_root / "ANONYMIZATION_REPORT.json").write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def finalize_report(destination_root: Path) -> None:
    """Mark the report as passed after the independent output scan."""
    path = destination_root / "ANONYMIZATION_REPORT.json"
    report = json.loads(path.read_text(encoding="utf-8"))
    report["validation"] = "pass"
    path.write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def write_checksums(destination_root: Path) -> int:
    """Write deterministic checksums for every artifact file except itself."""
    files = [
        path
        for path in sorted(destination_root.rglob("*"))
        if path.is_file() and path.name != "SHA256SUMS"
    ]
    lines = [
        f"{sha256(path)}  {path.relative_to(destination_root)}"
        for path in files
    ]
    (destination_root / "SHA256SUMS").write_text(
        "\n".join(lines) + "\n", encoding="utf-8"
    )
    return len(files)


def archive_format(archive_path: Path) -> str:
    """Return the requested archive format from a conservative suffix allowlist."""
    name = archive_path.name.lower()
    if name.endswith(".tar.gz") or name.endswith(".tgz"):
        return "tar.gz"
    if name.endswith(".zip"):
        return "zip"
    raise ValueError("Archive must end in .zip, .tar.gz, or .tgz.")


def write_deterministic_tar_archive(
    source_root: Path,
    archive_path: Path,
) -> None:
    """Create a gzip-compressed tar without local uid, gid, user, or timestamps."""
    archive_path.parent.mkdir(parents=True, exist_ok=True)
    with archive_path.open("wb") as raw_stream:
        with gzip.GzipFile(
            filename="", mode="wb", fileobj=raw_stream, mtime=0, compresslevel=9
        ) as compressed_stream:
            with tarfile.open(fileobj=compressed_stream, mode="w") as archive:
                paths = [source_root] + sorted(source_root.rglob("*"))
                for path in paths:
                    relative = path.relative_to(source_root)
                    archive_name = Path(source_root.name) / relative
                    info = archive.gettarinfo(str(path), arcname=str(archive_name))
                    info.uid = 0
                    info.gid = 0
                    info.uname = "anonymous"
                    info.gname = "anonymous"
                    info.mtime = 0
                    if path.is_file():
                        with path.open("rb") as stream:
                            archive.addfile(info, stream)
                    else:
                        archive.addfile(info)


def write_deterministic_zip_archive(
    source_root: Path,
    archive_path: Path,
) -> None:
    """Create a ZIP without source paths, local identities, comments, or timestamps."""
    archive_path.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(
        archive_path,
        mode="w",
        compression=zipfile.ZIP_DEFLATED,
        compresslevel=9,
        allowZip64=True,
    ) as archive:
        paths = [source_root] + sorted(source_root.rglob("*"))
        for path in paths:
            relative = path.relative_to(source_root)
            archive_name = (Path(source_root.name) / relative).as_posix()
            if path.is_dir():
                archive_name = archive_name.rstrip("/") + "/"
            info = zipfile.ZipInfo(
                archive_name,
                date_time=(1980, 1, 1, 0, 0, 0),
            )
            info.create_system = 3
            if path.is_dir():
                info.external_attr = ((stat.S_IFDIR | 0o755) << 16) | 0x10
                info.compress_type = zipfile.ZIP_STORED
                archive.writestr(info, b"")
            elif path.is_file():
                mode = stat.S_IMODE(path.stat().st_mode)
                info.external_attr = (stat.S_IFREG | mode) << 16
                info.compress_type = zipfile.ZIP_DEFLATED
                archive.writestr(
                    info,
                    path.read_bytes(),
                    compress_type=zipfile.ZIP_DEFLATED,
                    compresslevel=9,
                )
            else:
                raise RuntimeError(f"Unsupported archive entry: {path}")


def write_deterministic_archive(
    source_root: Path,
    archive_path: Path,
    format_name: str,
) -> None:
    """Write one of the explicitly supported deterministic archive formats."""
    if format_name == "tar.gz":
        write_deterministic_tar_archive(source_root, archive_path)
    elif format_name == "zip":
        write_deterministic_zip_archive(source_root, archive_path)
    else:
        raise ValueError(f"Unsupported archive format: {format_name}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--archive", type=Path)
    parser.add_argument(
        "--extra-token",
        action="append",
        default=[],
        help="Additional author, institution, host, or repository token to redact.",
    )
    args = parser.parse_args()

    output = args.output.expanduser().resolve()
    archive = args.archive.expanduser().resolve() if args.archive else None
    archive_kind = None
    if output.exists():
        parser.error(f"Refusing to overwrite existing output: {output}")
    if is_relative_to(output, SOURCE_ROOT) or is_relative_to(SOURCE_ROOT, output):
        parser.error("The anonymous output must be outside the source bundle.")
    if archive is not None:
        try:
            archive_kind = archive_format(archive)
        except ValueError as error:
            parser.error(str(error))
        if archive.exists():
            parser.error(f"Refusing to overwrite existing archive: {archive}")
        if is_relative_to(archive, output):
            parser.error("The archive must be outside the output directory.")

    output.parent.mkdir(parents=True, exist_ok=True)
    rules, dynamic_tokens = replacement_rules(args.extra_token)
    counts: dict[str, int] = {}
    with tempfile.TemporaryDirectory(
        prefix=".anonymous-build-", dir=output.parent
    ) as temporary:
        staging = Path(temporary) / output.name
        staging.mkdir()
        copied, sanitized_text_files, excluded_categories = copy_submission_files(
            staging, rules, counts
        )
        write_submission_readme(staging)
        write_source_manifest(staging)
        write_report(
            staging,
            copied,
            sanitized_text_files,
            counts,
            excluded_categories,
        )
        findings = forbidden_findings(staging, dynamic_tokens)
        if findings:
            raise RuntimeError(
                "Anonymous artifact scan failed:\n"
                + json.dumps(findings[:20], indent=2, ensure_ascii=False)
            )
        finalize_report(staging)
        checksum_entries = write_checksums(staging)
        # Scan again after adding the generated report and checksum manifest.
        findings = forbidden_findings(staging, dynamic_tokens)
        if findings:
            raise RuntimeError(
                "Final anonymous artifact scan failed:\n"
                + json.dumps(findings[:20], indent=2, ensure_ascii=False)
            )
        os.replace(staging, output)

    if archive is not None:
        write_deterministic_archive(output, archive, archive_kind)

    summary = {
        "status": "pass",
        "output": str(output),
        "files_in_checksum_manifest": checksum_entries,
        "archive": str(archive) if archive is not None else None,
        "archive_format": archive_kind,
        "archive_sha256": sha256(archive) if archive is not None else None,
    }
    print(json.dumps(summary, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
