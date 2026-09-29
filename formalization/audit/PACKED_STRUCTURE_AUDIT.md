# Concrete packed-controller structural bridge audit

`ForestSampling/PackedStructure.lean` compiles cleanly, and all 14 public
theorems were audited with `#print axioms`. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. No additional axioms or proof
placeholders were introduced.

The actual `Screening.returnedRow` from the verified screening pipeline
satisfies `ForestPeeling.ScreenContract` on the true residual graph under
the previously proved RT, UEN, bank feasibility, oracle row-TV, signal
margin, and separating-majority premises. The row-cardinality cap is
unconditional; low-degree exactness uses `ScreenSuccess`.

When every returned row is exact, `rowGraph_adj_iff` identifies the concrete
public `CappedController.rowGraph`: its edges are exactly the true edges
with both endpoints uncommitted. Thus its residual graph equals the true
residual graph and its whole graph is a subgraph of the true forest.
A successful empty peel set already implies this equality. Correct residual
graph equality persists through every actual fresh commit, independently
of sampled token values.

For the concrete `CappedController.terminalBatch`, correctness of the public
residual graph forces the forest branch and its smallest-public-label
component centroids. `terminalBatch_safe` proves actual
`ForestModel.BatchStructurallySafe`, and `terminalBatch_halves` proves the
actual child-to-parent component halving after every possible batch value.

`terminal_structurallySafe` proves `Program.StructurallySafe` for the actual
capped terminal program when every current component has size strictly less
than `2^extra`. The induction shows that zero extra fuel implies a completed
history; hence the hard guard cannot perform an unsafe commit. It uses the
original program, original batches, and actual history updates.
`terminal_structurallySafe_of_depth` discharges that component premise when
`extra >= ceil(log₂(N+1))` from the actual number of positions.

The complete packed-loop prefix-safety connection is continuing separately
in `PackedLoopStructure.lean`, consuming the actual failure markers and
`PrefixRepair.SafeBeforeStop`. This stable terminal module does not itself
claim that every reached screen succeeds, or that the initial loop's fuel
remains sufficient through every peeling phase. The separate loop proof
must establish those conditions and combine them with these completed
terminal results. Existing sampler, screen, and controller files remain
unchanged.
