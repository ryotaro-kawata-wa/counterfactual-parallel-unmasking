#!/usr/bin/env python3
"""Verify that the audited compiled manuscript inputs have not changed."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parents[2]
manifest = json.loads(Path(__file__).with_name("claim_inventory.json").read_text())
failures = []
for entry in manifest["compiled_tex_inputs"]:
    path = root / entry["source"]
    if not path.is_file():
        failures.append(f"Missing input: {entry['source']}")
    elif hashlib.sha256(path.read_bytes()).hexdigest() != entry["sha256"]:
        failures.append(f"Changed input: {entry['source']}")
if failures:
    raise SystemExit("Manuscript basis mismatch:\n" + "\n".join(failures))
print(f"Manuscript basis matches: {len(manifest['compiled_tex_inputs'])} TeX inputs.")
