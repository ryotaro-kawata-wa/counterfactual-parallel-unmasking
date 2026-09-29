# Actual packed sampler safety before the first failed screen

`ForestSampling/PackedLoopStructure.lean` is complete and compiles cleanly.
All 11 public theorems were checked with `#print axioms`; only `propext`,
`Classical.choice`, and `Quot.sound` occur. No additional axioms, `sorry`,
`admit`, or diagnostic trace commands remain.

The final theorem is
`PackedLoopStructure.samplerMarker_safeBeforeStop P M O C s nu signal`.
It proves `Program.PrefixRepair.SafeBeforeStop M O` for the **actual**
`PackedSampler.samplerMarker P M O blocks`, for every finite seed `blocks`.
Its premises are the existing model/oracle and public parameter conditions:

- `N > 0`, cutoff `D >= 9`;
- `P.phases = ForestIteration.phaseCap N D` and
  `P.extraRounds = ForestIteration.hardRoundCap N D - 1`;
- nonnegative row error and tail allowance, threshold in `[0,1]`, and the
  threshold-floor witness stored in `P`;
- `M.TailResponseRegular C s`, `M.EdgeNondegenerate signal`, feasible tail
  allowance `min 1 (C * threshold^s) <= nu`, and strict margin
  `4 * rowError + nu < signal`;
- actual TV accuracy of every frozen oracle row at the stored row-error
  radius.

There is no abstract structural-safety hypothesis, assumed high-count
recurrence, assumed correct returned-row function, or assumption that all
future screens succeed. The same theorem applies directly to
`PackedSampler.manuscriptParameters`; its two cap equalities are definitional.

`actualRows` is the exact standard returned-row function, including the
actual query-table replies and the public top-vote-score transcript.
`safeBeforeStop_markScreen` follows the real query schedule and passes
safety precisely to those rows. `safeBeforeStop_markPeel` follows the actual
frozen singleton list, proves every commit structurally safe, excludes its
hard guard when the available fuel covers the list, and supplies the
continuation with both its actual residual-set identity and the fuel
consumption bound. It includes skipped/already committed labels.

The main loop induction maintains two explicit, derived invariants:

    trueHighCount < (8/D)^(J - remainingPhases) * 2*N/(D+1)
    4*N*remainingPhases/D + centroidDepth N <= remainingExtraFuel.

Every successful screen satisfies the proved graph `ScreenContract`.
The next history has removed precisely the frozen peel set; an actual
induced-graph embedding proves high-count contraction. The real forest
degree sum bounds the actual list length by `4*N/D`, preserving enough
fuel for every subsequent phase and for the concrete centroid terminal
controller. At zero remaining phases, the exact logarithmic cap forces
all true residual degrees below the cutoff, so the final rows recover the
true residual graph. An empty peel set provides the same certificate
without waiting until the cap. The stable `PackedStructure` terminal proof
then excludes unsafe terminal fallback and proves safety for all possible
batch values.

At a failed screen the marker stops immediately, as defined in
`PackedFailure`; at every earlier commit, `SafeBeforeStop` requires actual
`BatchStructurallySafe` and safety of **all** continuation markers. Thus
the result is stronger than checking only completed paths with no failed
screen. It is the precise premise needed by `PrefixSafeRepair.repaired_safe`
and the actual seed-average TV/KL risk wrapper.

The final risk/parameter theorem is assembled by the parent from this
completed safety theorem, the completed actual failure probability bound,
and the separate oracle perturbation comparison. This file does not change
the sampler, any controller branch, the oracle model, target law, or seed law.
