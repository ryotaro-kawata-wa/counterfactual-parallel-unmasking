import ForestSampling.ScreeningProbes
import ForestSampling.ScreeningResponse
import ForestSampling.LocalMarkov

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace Screening

variable {N : ℕ} {V Color : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable [DecidableEq Color]

/-- The masked readout in a packed probe is justified by the actual chunk
definition, so the oracle row is a well-typed submitted-state readout. -/
noncomputable def probeReadout [LinearOrder V] (h : History N V)
    (B : Banks (N := N) (V := V)) (draft : Position N → V)
    (color : Position N → Color) (chunkSize : ℕ) (i j : ResidualVertex h)
    (column : B.Column) : MaskedPosition
      (probeState h B draft color (color i) (readoutChunk h color chunkSize j) column) :=
  ⟨j, by
    rw [MaskedState.mem_masked_iff, probeState_masked_iff]
    exact readout_mem_chunk h color chunkSize j
    exact readoutChunk_subset h color chunkSize j⟩

/-- Actual frozen-oracle reply used by one source/readout column comparison. -/
noncomputable def observedRow [LinearOrder V] (O : FrozenOracle N V)
    (h : History N V) (B : Banks (N := N) (V := V)) (draft : Position N → V)
    (color : Position N → Color) (chunkSize : ℕ) (i j : ResidualVertex h)
    (column : B.Column) : FinDist V :=
  O.row _ (probeReadout h B draft color chunkSize i j column)

/-- Separating packed probes have exactly the common draft-boundary rows
appearing in the target's RT and UEN assumptions. -/
theorem probe_exactRow_eq_boundary [LinearOrder V] (M : ForestModel N V)
    (h : History N V) (B : Banks (N := N) (V := V)) (draft : Position N → V)
    (color : Position N → Color) (chunkSize : ℕ) (i j : ResidualVertex h)
    (hij : i.val ≠ j.val) (hsep : Separating M h color i j) (column : B.Column) :
    (probeState h B draft color (color i) (readoutChunk h color chunkSize j) column).exactRow
      M.target M.target_positive (probeReadout h B draft color chunkSize i j column) =
      M.target.boundaryRow M.target_positive i j (B.packedColumn draft column i)
        (fixedBoundary h draft i j) := by
  let y := probeState h B draft color (color i) (readoutChunk h color chunkSize j) column
  let z := MaskedState.boundaryState i.val j.val (B.packedColumn draft column i)
    (fixedBoundary h draft i j)
  have hy : y j = none :=
    ((y.mem_masked_iff j).mp (probeReadout h B draft color chunkSize i j column).property)
  calc
    _ = z.exactRow M.target M.target_positive ⟨j, by simp [z]⟩ :=
      M.exactRow_eq_of_neighbors_observed y z j hy (by simp [z])
        (probe_boundary_neighbors M h B draft color chunkSize i j hij hsep column)
    _ = _ := MaskedState.exactRow_boundaryState M hij _ _

omit [DecidableEq Color] in
/-- Complete-boundary rows do not respond to a nonneighbor source. -/
theorem boundaryRow_eq_of_not_adj (M : ForestModel N V) {i j : Position N}
    (hij : i ≠ j) (hnonedge : ¬ M.graph.Adj i j)
    (z : CompleteBoundary N V i j) (a b : V) :
    M.target.boundaryRow M.target_positive i j a z =
      M.target.boundaryRow M.target_positive i j b z := by
  rw [← MaskedState.exactRow_boundaryState M hij a z,
    ← MaskedState.exactRow_boundaryState M hij b z]
  apply M.exactRow_eq_of_neighbors_observed _ _ j (by simp) (by simp)
  intro v hv
  have hvj : v ≠ j := hv.ne.symm
  have hvi : v ≠ i := by
    intro heq
    apply hnonedge
    simpa [heq] using hv.symm
  exact ⟨z ⟨v, hvi, hvj⟩, by simp [MaskedState.boundaryState, hvj, hvi],
    by simp [MaskedState.boundaryState, hvj, hvi]⟩

/-- A vote is deliberately zero when source/readout colors agree. For
different colors it compares the actual observed finite-row diameter. -/
noncomputable def Vote [LinearOrder V] (O : FrozenOracle N V)
    (h : History N V) (B : Banks (N := N) (V := V)) (draft : Position N → V)
    (color : Position N → Color) (chunkSize : ℕ) (ε : ℝ) (i j : ResidualVertex h) : Prop :=
  color i ≠ color j ∧
    2 * ε < rowDiameter (observedRow O h B draft color chunkSize i j)

theorem not_vote_of_separating_nonedge [LinearOrder V] (M : ForestModel N V)
    (O : FrozenOracle N V) (h : History N V) (B : Banks (N := N) (V := V))
    (draft : Position N → V) (color : Position N → Color) (chunkSize : ℕ) (ε : ℝ)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.tv (y.exactRow M.target M.target_positive j) (O.row y j) ≤ ε)
    (i j : ResidualVertex h) (hij : i.val ≠ j.val) (hsep : Separating M h color i j)
    (hnonedge : ¬ M.graph.Adj i.val j.val) :
    ¬ Vote O h B draft color chunkSize ε i j := by
  rintro ⟨_, hvote⟩
  have hsmall := rowDiameter_le_of_common_exact
    (observedRow O h B draft color chunkSize i j)
    (M.target.boundaryRow M.target_positive i j (B.tail i) (fixedBoundary h draft i j)) ε
    (fun column ↦ ?_)
  · linarith
  · have hr := hrows _ (probeReadout h B draft color chunkSize i j column)
    rw [probe_exactRow_eq_boundary M h B draft color chunkSize i j hij hsep column] at hr
    rw [boundaryRow_eq_of_not_adj M hij hnonedge _ (B.packedColumn draft column i) (B.tail i)] at hr
    exact hr

/-- Every separating true-edge coloring casts a positive vote. This uses
the actual all-mask banks, packed probes, RT, UEN, and frozen row error. -/
theorem vote_of_separating_edge [LinearOrder V] (M : ForestModel N V)
    (O : FrozenOracle N V) (h : History N V) (draft : Position N → V)
    (color : Position N → Color) (chunkSize : ℕ)
    (C s t ε ν signal : ℝ)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ε)
    (hε : 0 ≤ ε) (hν : 0 ≤ ν) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hRT : M.TailResponseRegular C s) (hUEN : M.EdgeNondegenerate signal)
    (hfeasible : min 1 (C * t ^ s) ≤ ν) (hmargin : 4 * ε + ν < signal)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.tv (y.exactRow M.target M.target_positive j) (O.row y j) ≤ ε)
    (i j : ResidualVertex h) (hsep : Separating M h color i j)
    (hedge : M.graph.Adj i.val j.val) :
    Vote O h (Banks.ofOracle O t ε hfloor) draft color chunkSize ε i j := by
  let B := Banks.ofOracle O t ε hfloor
  refine ⟨separating_edge_colors_ne M h color i j hsep hedge, ?_⟩
  refine rowDiameter_gt_of_edge M hedge (fixedBoundary h draft i j)
    (B.bank i) (B.tail i) (B.tail_not_mem i) (fun column ↦ B.packedColumn draft column i)
    (observedRow O h B draft color chunkSize i j) ?_ ε ν signal hε hν hUEN hmargin ?_ ?_
  · intro a ha
    rcases Finset.mem_insert.mp ha with ha | ha
    · exact ⟨none, by simp [ha]⟩
    · exact B.packedColumn_covers_bank draft i a ha
  · intro column
    have hr := hrows _ (probeReadout h B draft color chunkSize i j column)
    rwa [probe_exactRow_eq_boundary M h B draft color chunkSize i j hedge.ne hsep column] at hr
  · intro a ha b hb
    exact omitted_response_le M O C s t ε ν hRT ht0 ht1 hfeasible hrows hedge.ne
      (fixedBoundary h draft i j) a b ha hb

end Screening
end ForestSampling
