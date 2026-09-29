# Final named-claim validation — 27 September 2026

Reproducible checks completed after all final theorem modules were imported:

- `lake build`: success, 8,880 jobs; 173 local proof modules in the root's
  transitive import closure. Remaining output consists of style/unused-variable
  linter warnings, not unsolved proofs.
- `lake env lean AuditAxioms.lean`: all 4,716 project declarations passed the
  transitive audit. Only `propext`, `Classical.choice`, `Quot.sound` occur.
- `python3 audit/check_manuscript_basis.py`: all 61 compiled TeX input hashes
  match the recorded mathematical/layout baseline.
- `python3 audit/check_claim_references.py`: all 122 distinct declaration
  references in the inventory resolve in the built root environment.
- `git diff --check`: no whitespace errors.

Toolchain: Lean 4.33.0; Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`; transitive versions fixed by the
committed `lake-manifest.json`. Existing local dependency caches were used.
No runtime installation or dependency update was needed.

Inventory status: 36 named proof claims mapped to proved formal theorem
bundles; 24 definition/assumption interfaces with correspondence audits; one
additional formalized KL definition. The 4,716 declaration count includes
supporting definitions and generated auxiliaries and is not a paper-theorem
count. The TeX-to-Lean mapping remains an explicit semantic audit boundary.

Independent main and comparison-path correspondence reviews found no remaining
mathematical mismatch in their stated review scopes. Their evidence and limits
are recorded in `FINAL_MAIN_CORRESPONDENCE_REVIEW.md` and
`PATH_FINAL_CORRESPONDENCE.md`. Unlabelled prose, external literature guarantees,
scientific experiment conclusions, and omitted optional manuscript sections
are not certified by the named-claim count.

The mathematical TeX source was unchanged. arXiv layout remains a separate
local branch; no push or arXiv submission was performed in this verification.
