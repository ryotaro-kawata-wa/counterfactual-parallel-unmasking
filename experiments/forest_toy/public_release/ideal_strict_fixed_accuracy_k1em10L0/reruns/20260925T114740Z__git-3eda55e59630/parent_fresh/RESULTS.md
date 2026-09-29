# Ideal capless fixed-accuracy result

- N grid: `[8192, 10240, 12288, 14336, 16384]`.
- Target: exact oracle, constant edge strengths, `E[W/X]=1`.
- Proposal: no external query cap; Q includes preprocessing, counterfactual queries, and commit rounds once each.
- Random: tuned at the same per-tree K_star, with no 0.5 margin or one-step cushion.
- Fresh 6/6 proposal cells: `20/20`.
- Fresh 6/6 random cells: `16/20`.

The figure is descriptive; no inferential scaling claim is added.
