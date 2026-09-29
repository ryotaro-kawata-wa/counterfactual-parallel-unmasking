# Counterfactual Probing for Parallel Unmasking with Hidden Forest Structure

Research artifacts accompanying the paper by **Ryotaro Kawata, Satoshi Hayakawa,
and Taiji Suzuki**. The `arxiv-v1` tag fixes the source, formalization, and
experiment records for this release.

| Material | Start here |
| --- | --- |
| Paper | [Manuscript PDF](manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/output/pdf/arxiv_preprint.pdf) |
| arXiv upload | [Source ZIP](manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/output/arxiv/arxiv_source.zip) |
| Lean 4 proofs and exact verification scope | [Formalization guide](formalization/README.md) |
| Claim-to-proof correspondence | [Claim inventory](formalization/audit/claim_inventory.json) |
| Figure 3 code, frozen inputs, and saved results | [Experiment guide](experiments/forest_toy/public_release/ideal_strict_fixed_accuracy_k1em10L0/README.md) |
| Independent complete rerun | [Rerun report](experiments/forest_toy/public_release/ideal_strict_fixed_accuracy_k1em10L0/reruns/20260925T114740Z__git-3eda55e59630/README.md) |
| Checks of this public snapshot | [Release validation](verification/README.md) |

## Reproduce the formal verification

Install Lean through elan, then run:

```sh
cd formalization
lake exe cache get
lake build
lake env lean AuditAxioms.lean
python3 audit/check_manuscript_basis.py
python3 audit/check_claim_references.py
```

`lean-toolchain` pins Lean 4.33.0 and `lake-manifest.json` pins Mathlib and its
dependencies. Please do not run `lake update` for reproduction.
The formalization covers 36 named mathematical proof claims under their
formalized assumptions. The manuscript-to-Lean correspondence is audited
separately; the count does not certify all prose, citations, or experiments.
The axiom audit allows only `propext`, `Classical.choice`, and `Quot.sound`.
No local build or dependency cache is included. See the release validation
record for the cache reuse and audit details of this export.

## Reproduce the experiments

Use Python 3.10–3.12 and a C compiler. From the experiment directory:

```sh
cd experiments/forest_toy/public_release/ideal_strict_fixed_accuracy_k1em10L0
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
./verify_bundled_results.sh
./smoke_test.sh
```

For a complete new run, follow the experiment guide and `reproduce_fresh.sh`.
The release includes saved scalar results and compressed records from an
independent full rerun. Large regenerable NPZ intermediates are omitted.
Historical machine names and source-commit IDs in provenance records describe
the original runs; reproduction uses the files and dependency pins here.

## Build the paper

With TeX Live and latexmk installed:

```sh
cd manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures
make arxiv
make arxiv-package
```

The source-directory structure is retained so the manuscript fingerprints and
claim inventory resolve without path translation. The submission ZIP contains
the paper's TeX inputs, figures, bibliography, and build configuration. Code is
distributed in this repository rather than as arXiv ancillary files.

## License

The original Lean and experiment code, supporting scripts, and software
documentation are available under the [MIT License](LICENSE). The manuscript
and research figures are not covered by this software license. Dependencies
and third-party material retain their respective licenses.

## Citation

Please cite the accompanying paper when using these artifacts. GitHub's citation
panel provides the software record. An arXiv identifier will be added after the
article is announced.
