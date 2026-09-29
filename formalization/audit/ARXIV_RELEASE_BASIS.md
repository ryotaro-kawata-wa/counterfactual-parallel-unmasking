# Integrated arXiv manuscript basis — 28 September 2026

The arXiv branch now combines the current manuscript, the tracked experiment
reproduction bundle, and the complete Lean development from `d561c28b`.
No Lean proof source or mathematical TeX statement was changed by integration.

## Deliberately audited presentation changes

The original verification basis is arXiv commit
`1507791fd7c1137c77ec139cc0b73b5765f1464b`, mathematically identical to pushed
ICLR commit `8a8c185375bd4de48c2ef52807da0c3cc00e15ac`. Its PDF hash and all
61 input hashes are preserved in `manuscript_basis_2026-09-26.json`.

The integrated inventory targets the ERATO-acknowledgment source checkpoint
`6ecca8a97a288478f50317161d5fbfe8b3e43022`, with the following reviewed differences:

- 58 of the original 61 compiled TeX inputs are byte-identical.
- `main.tex` adds only the confirmed author/affiliation/email block, PDF metadata,
  and an arXiv-only acknowledgment input after the main text.
- `main_experiments.tex` selects the Figure 3 presentation derivative in arXiv
  builds and corrects its caption unit from rounds to submissions. The plotted
  numerical values and experiment statements are unchanged.
- `src/arxiv_preamble.tex` removes paragraph indentation (including the abstract)
  and adds a modest 4pt paragraph gap with `parskip`. It changes presentation only.
- `src/sections/acknowledgments.tex` is one new compiled input containing only
  the supplied acknowledgments, including the revised SH funding/program wording
  and the author-supplied ERATO acknowledgment (JPMJER2601) after the TS sentence.
  It contains no mathematical claim.

Thus the current fingerprint contains **62 TeX inputs**. The inventory's
61 statement entries, named-claim classifications, and Lean declaration mappings
are unchanged. Every theorem/proof source retains its original hash. The current
PDF has 97 pages; the main text still occupies 9 pages.

`check_manuscript_basis.py` still rejects any mismatch against the recorded
current hashes; its checking logic has not been relaxed. A future source edit
requires another deliberate correspondence review, not automatic hash refresh.

The author/figure checks and ZIP-only build are recorded in the repository's
`ARXIV_PREPRINT.md` and `ARXIV_SOURCE_PACKAGE.md`. Paragraph layout checks are
recorded in `audits/arxiv_paragraph_spacing_2026-09-28/verification.json`.
The subsequent SH acknowledgment revision is checked in
`audits/arxiv_sh_acknowledgment_2026-09-28/verification.json`. The later ERATO
addition is checked in `audits/arxiv_erato_acknowledgment_2026-09-28/verification.json`.
This presentation update does not extend Lean's claim coverage to prose, citations, acknowledgments, or
scientific experiment conclusions.


## AI-use disclosure and reference compatibility — 29 September 2026

The current fingerprint is deliberately updated from the September 28 snapshot.
Only two compiled TeX inputs change in this revision:

- `src/sections/ai_use_statement.tex` states that AI assistance was used to
  formalize the manuscript's named mathematical claims in Lean 4, that Lean's
  kernel checked the formal proofs, and that manuscript correspondence was
  audited separately. This describes the scope already recorded in
  `FINAL_VALIDATION.md`; it does not expand the proved claim set.
- `main.tex` loads `amsthm` before `cleveref` and moves the unchanged theorem
  declarations after `cleveref`. The arXiv-generated PDF had rendered shared-
  counter Definition/Lemma/Assumption references as Theorem. The edit follows
  cleveref's documented load order and changes no mathematical statement.

All 62 compiled input hashes have been checked; the 61 inventory entries,
36 named proof claims, and Lean declaration mappings are unchanged. Every
mathematical statement/proof source and every Lean source is unchanged.
The previously completed kernel/axiom audit remains the proof evidence; the
Lean kernel was not rerun for these prose/preamble edits.

The new ZIP builds in an isolated directory and matches the current 97-page
PDF on every page. All 392 cleveref reference types and all displayed label
values match the preceding local build. A 2025-06-01 LaTeX-kernel rollback
also matches, but uses the local 2026 package set and is not the arXiv runtime.
The old load order also passes that partial emulation. Re-uploading to arXiv
and reviewing its PDF remains necessary to confirm the compatibility fix.


## Public-code availability — 29 September 2026

The manuscript now names the `arxiv-v1` snapshot of the public research-artifact
repository, `ryotaro-kawata-wa/counterfactual-parallel-unmasking`. One new input,
`src/sections/code_availability.tex`, contains only that availability statement;
`main.tex` includes it for the arXiv presentation. The fingerprint has 63 TeX
inputs. All named mathematical claims, assumptions, proof sources, and Lean
sources are unchanged. The published snapshot preserves this source layout so
the same manuscript-basis check runs without path rewriting.
