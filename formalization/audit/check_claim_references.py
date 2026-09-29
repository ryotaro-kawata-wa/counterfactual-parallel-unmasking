#!/usr/bin/env python3
"""Please run after lake build to verify all inventory declaration references."""
from __future__ import annotations

import json
import os
import shutil
import subprocess
import tempfile
from pathlib import Path

formalization = Path(__file__).resolve().parents[1]
manifest = json.loads(Path(__file__).with_name('claim_inventory.json').read_text())
references: set[str] = set()
for claim in manifest['claims']:
    declarations = claim.get('lean_declarations', [])
    if claim['coverage'] == 'proved' and not declarations:
        raise SystemExit(f"Proved claim has no Lean references: {claim['label']}")
    for name in declarations:
        references.add(name if name.startswith('ForestSampling.') else f'ForestSampling.{name}')

lake = os.environ.get('FOREST_LAKE') or shutil.which('lake')
if lake is None:
    fallback = Path.home() / '.elan/bin/lake'
    if fallback.is_file():
        lake = str(fallback)
if lake is None:
    raise SystemExit('Please place the pinned lake executable on PATH or set FOREST_LAKE.')

source = '''import ForestSampling
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : Array String := #[NAMES]
  let mut missing : Array String := #[]
  for spelling in names do
    unless env.contains spelling.toName do
      missing := missing.push spelling
  unless missing.isEmpty do
    throwError "Inventory declarations are not imported: {missing}"
  logInfo m!"Inventory references resolve: {names.size} declarations."
'''.replace('NAMES', ', '.join(json.dumps(name) for name in sorted(references)))
with tempfile.TemporaryDirectory(prefix='forest-claim-audit-') as directory:
    path = Path(directory) / 'ClaimReferences.lean'
    path.write_text(source)
    result = subprocess.run([lake, 'env', 'lean', str(path)], cwd=formalization, check=False)
    raise SystemExit(result.returncode)
