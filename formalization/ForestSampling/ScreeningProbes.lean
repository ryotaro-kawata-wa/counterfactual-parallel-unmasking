import ForestSampling.ScreeningPreprocess

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace MaskedState

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The fully observed source and boundary state, with only its readout
masked. This state relates packed probes to the manuscript's RT/UEN rows. -/
def boundaryState (i j : Position N) (a : V) (z : CompleteBoundary N V i j) :
    MaskedState N V := fun k ↦
  if hkj : k = j then none else if hki : k = i then some a else some (z ⟨k, hki, hkj⟩)

omit [Fintype V] [DecidableEq V] [Nonempty V] in
@[simp] theorem boundaryState_readout (i j : Position N) (a : V)
    (z : CompleteBoundary N V i j) : boundaryState i j a z j = none := by
  simp [boundaryState]

omit [Fintype V] [DecidableEq V] [Nonempty V] in
theorem boundaryState_agrees_iff {i j : Position N} (hij : i ≠ j) (a : V)
    (z : CompleteBoundary N V i j) (x : Configuration N V) :
    (boundaryState i j a z).Agrees x ↔ CompleteBoundary.Event i j a z x := by
  constructor
  · intro hx
    constructor
    · exact hx i a (by simp [boundaryState, hij])
    · intro k
      exact hx k (z k) (by simp [boundaryState, k.2.1, k.2.2])
  · rintro ⟨hi, hz⟩ k b hb
    by_cases hkj : k = j
    · simp [boundaryState, hkj] at hb
    by_cases hki : k = i
    · simp [boundaryState, hki] at hb
      simpa [hki, hb] using hi
    · simp [boundaryState, hkj, hki] at hb
      exact (hz ⟨k, hki, hkj⟩).trans hb

theorem exactRow_boundaryState (M : ForestModel N V) {i j : Position N}
    (hij : i ≠ j) (a : V) (z : CompleteBoundary N V i j) :
    (boundaryState i j a z).exactRow M.target M.target_positive
      ⟨j, by simp⟩ = M.target.boundaryRow M.target_positive i j a z := by
  apply FinDist.conditionalMap_congr
  · exact boundaryState_agrees_iff hij a z
  · intro x
    rfl

end MaskedState

namespace Screening

variable {N : ℕ} {V Color : Type*} [Fintype V] [DecidableEq V]
variable [DecidableEq Color]

/-- One public color class of the current residual positions. -/
def colorClass (h : History N V) (color : Position N → Color) (c : Color) :
    Finset (Position N) := h.uncommitted.filter (fun j ↦ color j = c)

/-- The zero-based rank of a position in its color class, in the public
position order. -/
def colorRank (h : History N V) (color : Position N → Color) (j : Position N) : ℕ :=
  ((colorClass h color (color j)).filter (fun k ↦ k < j)).card

/-- The deterministic chunk containing a residual readout. Equal quotients
of public color-class ranks form the manuscript's consecutive chunks. -/
def readoutChunk (h : History N V) (color : Position N → Color) (chunkSize : ℕ)
    (j : ResidualVertex h) : Finset (Position N) :=
  (colorClass h color (color j)).filter
    (fun k ↦ colorRank h color k / chunkSize = colorRank h color j / chunkSize)

omit [Fintype V] [DecidableEq V] in
theorem readout_mem_chunk (h : History N V) (color : Position N → Color)
    (chunkSize : ℕ) (j : ResidualVertex h) : j.val ∈ readoutChunk h color chunkSize j := by
  simp [readoutChunk, colorClass, j.property]

omit [Fintype V] [DecidableEq V] in
theorem readoutChunk_subset (h : History N V) (color : Position N → Color)
    (chunkSize : ℕ) (j : ResidualVertex h) :
    readoutChunk h color chunkSize j ⊆ h.uncommitted := by
  intro k hk
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).1

omit [Fintype V] [DecidableEq V] in
theorem color_eq_of_mem_chunk (h : History N V) (color : Position N → Color)
    (chunkSize : ℕ) (j : ResidualVertex h) {k : Position N}
    (hk : k ∈ readoutChunk h color chunkSize j) : color k = color j :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2

/-- The actual submitted packed probe. It keeps commits fixed, masks the
readout chunk, changes only the selected source color, and pads by the
already fixed draft. -/
noncomputable def probeState [LinearOrder V] (h : History N V)
    (B : Banks (N := N) (V := V)) (draft : Position N → V)
    (color : Position N → Color) (sourceColor : Color)
    (chunk : Finset (Position N)) (column : B.Column) : MaskedState N V := fun k ↦
  if hk : k ∈ h.committed then some (h.value ⟨k, hk⟩)
  else if k ∈ chunk then none
  else if color k = sourceColor then some (B.packedColumn draft column k)
  else some (draft k)

omit [Fintype V] [DecidableEq V] in
theorem probeState_respects [LinearOrder V] (h : History N V)
    (B : Banks (N := N) (V := V)) (draft : Position N → V)
    (color : Position N → Color) (sourceColor : Color)
    (chunk : Finset (Position N)) (column : B.Column) :
    (probeState h B draft color sourceColor chunk column).RespectsHistory h := by
  intro k
  simp [probeState]

omit [Fintype V] in
theorem probeState_masked_iff [LinearOrder V] (h : History N V)
    (B : Banks (N := N) (V := V)) (draft : Position N → V)
    (color : Position N → Color) (sourceColor : Color)
    (chunk : Finset (Position N)) (hfresh : chunk ⊆ h.uncommitted)
    (column : B.Column) (k : Position N) :
    probeState h B draft color sourceColor chunk column k = none ↔ k ∈ chunk := by
  by_cases hk : k ∈ h.committed
  · have hnot : k ∉ chunk := fun hmem ↦
      ((h.mem_uncommitted_iff k).mp (hfresh hmem)) hk
    simp [probeState, hk, hnot]
  · simp [probeState, hk]
    split <;> simp_all

/-- The complete boundary used in every coloring of this screen. It depends
on the fixed history and draft, and hence not on current or future colors. -/
def fixedBoundary (h : History N V) (draft : Position N → V)
    (i j : Position N) : CompleteBoundary N V i j := fun k ↦
  if hk : k.val ∈ h.committed then h.value ⟨k, hk⟩ else draft k

/-- Analysis-only pair separation. The implementation never evaluates this
predicate because it contains the hidden residual adjacency relation. -/
def Separating (M : ForestModel N V) (h : History N V)
    (color : Position N → Color) (i j : ResidualVertex h) : Prop :=
  (∀ v : ResidualVertex h, M.graph.Adj j.val v.val → color v ≠ color j) ∧
  (∀ v : ResidualVertex h, M.graph.Adj j.val v.val → v.val ≠ i.val → color v ≠ color i)

omit [DecidableEq Color] in
theorem separating_edge_colors_ne (M : ForestModel N V) (h : History N V)
    (color : Position N → Color) (i j : ResidualVertex h)
    (hsep : Separating M h color i j) (hedge : M.graph.Adj i.val j.val) :
    color i ≠ color j := hsep.1 i hedge.symm

/-- A separating coloring reveals every neighbor of the readout at the
same value as the common complete boundary and selected source token. -/
theorem probe_boundary_neighbors [LinearOrder V] (M : ForestModel N V)
    (h : History N V) (B : Banks (N := N) (V := V)) (draft : Position N → V)
    (color : Position N → Color) (chunkSize : ℕ) (i j : ResidualVertex h)
    (hij : i.val ≠ j.val) (hsep : Separating M h color i j) (column : B.Column) :
    ∀ v, M.graph.Adj j.val v → ∃ a,
      probeState h B draft color (color i) (readoutChunk h color chunkSize j) column v = some a ∧
      MaskedState.boundaryState i j (B.packedColumn draft column i)
        (fixedBoundary h draft i j) v = some a := by
  intro v hv
  have hvj : v ≠ j.val := hv.ne.symm
  by_cases hvc : v ∈ h.committed
  · have hvi : v ≠ i.val := by
      intro heq
      exact ((h.mem_uncommitted_iff i.val).mp i.property) (heq ▸ hvc)
    refine ⟨h.value ⟨v, hvc⟩, ?_, ?_⟩
    · simp [probeState, hvc]
    · simp [MaskedState.boundaryState, hvj, hvi, fixedBoundary, hvc]
  · have hvr : v ∈ h.uncommitted := (h.mem_uncommitted_iff v).mpr hvc
    have hnochunk : v ∉ readoutChunk h color chunkSize j := by
      intro hmem
      exact hsep.1 ⟨v, hvr⟩ hv (color_eq_of_mem_chunk h color chunkSize j hmem)
    by_cases hvi : v = i.val
    · refine ⟨B.packedColumn draft column i, ?_, ?_⟩
      · simp only [probeState, dif_neg hvc, if_neg hnochunk]
        simp [hvi]
      · simp [MaskedState.boundaryState, hvi, hij]
    · have hcolors := hsep.2 ⟨v, hvr⟩ hv hvi
      refine ⟨draft v, ?_, ?_⟩
      · simp [probeState, hvc, hnochunk, hcolors]
      · simp [MaskedState.boundaryState, hvj, hvi, fixedBoundary, hvc]

end Screening
end ForestSampling
