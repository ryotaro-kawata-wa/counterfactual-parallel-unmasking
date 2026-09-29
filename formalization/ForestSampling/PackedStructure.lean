import ForestSampling.PackedSampler
import ForestSampling.ForestIteration
import ForestSampling.ForestConditionals

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling.PackedStructure

noncomputable section
attribute [local instance] Classical.propDecidable

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

omit [Nonempty V] in
/-- The neighbor rows used in the screening proof are the actual neighbor
finsets of the true residual graph. -/
theorem residualNeighbors_eq (M : ForestModel N V) (h : History N V) (j : ResidualVertex h) :
    Screening.residualNeighbors M h j = (residualGraph M.graph h).neighborFinset j := by
  ext i
  rw [(residualGraph M.graph h).mem_neighborFinset]
  simp [Screening.residualNeighbors, residualGraph, M.graph.adj_comm]

/-- The proved deterministic returned-row laws provide exactly the graph
contract required by the finite forest peeling lemmas. -/
theorem screenContract_of_returnedRow {Color ι Transcript : Type*}
    [Fintype ι] [DecidableEq ι] [DecidableEq Color] [LinearOrder V]
    (M : ForestModel N V) (O : FrozenOracle N V)
    (h : History N V) (draft : Position N → V) (colors : ι → Position N → Color)
    (q D : ℕ) (C s t ε ν signal : ℝ)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ε)
    (hε : 0 ≤ ε) (hν : 0 ≤ ν) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hRT : M.TailResponseRegular C s) (hUEN : M.EdgeNondegenerate signal)
    (hfeasible : min 1 (C * t ^ s) ≤ ν) (hmargin : 4 * ε + ν < signal)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.tv (y.exactRow M.target M.target_positive j) (O.row y j) ≤ ε)
    (hsuccess : Screening.ScreenSuccess M h colors D)
    (selector : PublicRowSelector (ResidualVertex h) Transcript) (transcript : Transcript) :
    ForestPeeling.ScreenContract (residualGraph M.graph h) D
      (Screening.returnedRow O h (Screening.Banks.ofOracle O t ε hfloor) draft colors q D ε
        selector transcript) := by
  constructor
  · exact Screening.returnedRow_card_le O h _ draft colors q D ε selector transcript
  · intro j hj
    have hdegree : (Screening.residualNeighbors M h j).card ≤ D := by
      simpa only [residualNeighbors_eq, SimpleGraph.card_neighborFinset_eq_degree] using hj
    rw [Screening.returnedRow_eq_neighbors M O h draft colors q D C s t ε ν signal
      hfloor hε hν ht0 ht1 hRT hUEN hfeasible hmargin hrows hsuccess selector transcript j hdegree]
    exact residualNeighbors_eq M h j

omit [Fintype V] [Nonempty V] in
/-- Once all rows are exact, the public undirected graph contains precisely
the true edges whose two endpoints remain uncommitted. -/
theorem rowGraph_adj_iff (G : SimpleGraph (Position N)) (h : History N V)
    (rows : ResidualVertex h → Finset (ResidualVertex h))
    (hrows : ∀ j, rows j = (residualGraph G h).neighborFinset j) (i j : Position N) :
    (CappedController.rowGraph h rows).Adj i j ↔
      i ∈ h.uncommitted ∧ j ∈ h.uncommitted ∧ G.Adj i j := by
  change (i ≠ j ∧ ((∃ hi hj, (⟨j, hj⟩ : ResidualVertex h) ∈ rows ⟨i, hi⟩) ∨
    (∃ hj hi, (⟨i, hi⟩ : ResidualVertex h) ∈ rows ⟨j, hj⟩))) ↔ _
  constructor
  · rintro ⟨_, ⟨hi, hj, he⟩ | ⟨hj, hi, he⟩⟩
    · rw [hrows] at he
      exact ⟨hi, hj, ((residualGraph G h).mem_neighborFinset _ _).mp he⟩
    · rw [hrows] at he
      exact ⟨hi, hj, (((residualGraph G h).mem_neighborFinset _ _).mp he).symm⟩
  · rintro ⟨hi, hj, he⟩
    refine ⟨he.ne, Or.inl ⟨hi, hj, ?_⟩⟩
    rw [hrows]
    exact ((residualGraph G h).mem_neighborFinset _ _).mpr he

omit [Fintype V] [Nonempty V] in
/-- Exact rows give equality of the public and true residual graphs. -/
theorem residual_rowGraph_eq (G : SimpleGraph (Position N)) (h : History N V)
    (rows : ResidualVertex h → Finset (ResidualVertex h))
    (hrows : ∀ j, rows j = (residualGraph G h).neighborFinset j) :
    residualGraph (CappedController.rowGraph h rows) h = residualGraph G h := by
  ext i j
  change (CappedController.rowGraph h rows).Adj i.1 j.1 ↔ G.Adj i.1 j.1
  simp only [rowGraph_adj_iff G h rows hrows, i.2, j.2, true_and]

omit [Fintype V] [Nonempty V] in
/-- The complete public graph from exact rows is a subgraph of the true
forest, with already committed positions isolated. -/
theorem rowGraph_le (G : SimpleGraph (Position N)) (h : History N V)
    (rows : ResidualVertex h → Finset (ResidualVertex h))
    (hrows : ∀ j, rows j = (residualGraph G h).neighborFinset j) :
    CappedController.rowGraph h rows ≤ G := by
  intro i j he
  exact ((rowGraph_adj_iff G h rows hrows i j).mp he).2.2

omit [Nonempty V] in
/-- A successful empty peel set already certifies every returned row,
without waiting until the numerical phase cap. -/
theorem residual_rowGraph_eq_of_empty_peel (M : ForestModel N V) (h : History N V)
    (D : ℕ) (hD : 4 ≤ D) (rows : ResidualVertex h → Finset (ResidualVertex h))
    (hrows : ForestPeeling.ScreenContract (residualGraph M.graph h) D rows)
    (hp : ForestPeeling.peelSet D rows = ∅) :
    residualGraph (CappedController.rowGraph h rows) h = residualGraph M.graph h :=
  residual_rowGraph_eq M.graph h rows
    (ForestPeeling.rows_exact_of_peelSet_empty (M.graph_acyclic.induce _) hrows hD hp)

omit [Fintype V] [Nonempty V] in
/-- Correctness of a public residual graph persists under every subsequent
history that deletes more vertices, regardless of the committed token values. -/
theorem residual_eq_of_subset (G H : SimpleGraph (Position N)) (h h' : History N V)
    (heq : residualGraph G h = residualGraph H h) (hsub : h'.uncommitted ⊆ h.uncommitted) :
    residualGraph G h' = residualGraph H h' := by
  ext i j
  exact iff_of_eq (congrFun (congrFun (SimpleGraph.ext_iff.mp heq)
    ⟨i.1, hsub i.2⟩) ⟨j.1, hsub j.2⟩)

/-- The actual fresh commit transition includes its residual graph into the
previous one; this is independent of the batch's sampled values. -/
def appendEmbedding (G : SimpleGraph (Position N)) (h : History N V)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted) (z : batch → V) :
    residualGraph G (h.appendBatch batch fresh z) ↪g residualGraph G h :=
  G.induceHomOfLE (fun _ hi ↦ by
    rw [History.appendBatch_uncommitted] at hi
    exact (Finset.mem_sdiff.mp hi).1)

omit [Fintype V] [Nonempty V] in
/-- The public residual graph remains correct after any fresh commit. -/
theorem residual_eq_append (G H : SimpleGraph (Position N)) (h : History N V)
    (heq : residualGraph G h = residualGraph H h)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted) (z : batch → V) :
    residualGraph G (h.appendBatch batch fresh z) = residualGraph H (h.appendBatch batch fresh z) :=
  residual_eq_of_subset G H h _ heq (by rw [History.appendBatch_uncommitted]; exact Finset.sdiff_subset)

omit [Nonempty V] in
/-- Mapping one chosen vertex per public component back to original labels
produces a safe true-forest batch whenever the public residual graph is correct. -/
theorem componentBatch_safe (M : ForestModel N V) (G : SimpleGraph (Position N)) (h : History N V)
    (heq : residualGraph G h = residualGraph M.graph h)
    (pick : (C : (residualGraph G h).ConnectedComponent) → C)
    (fresh : (ForestCentroid.componentBatch (residualGraph G h) pick).map
      (Function.Embedding.subtype _) ⊆ h.uncommitted) :
    M.BatchStructurallySafe h
      ((ForestCentroid.componentBatch (residualGraph G h) pick).map (Function.Embedding.subtype _)) fresh := by
  intro i j hij
  obtain ⟨u, hu, hui⟩ := Finset.mem_map.mp i.2
  obtain ⟨v, hv, hvj⟩ := Finset.mem_map.mp j.2
  have he : (residualGraph G h).Reachable u v := by
    rw [heq]
    apply SimpleGraph.ConnectedComponent.exact
    have hui' : u = (⟨i.1, fresh i.2⟩ : ResidualVertex h) := Subtype.ext hui
    have hvj' : v = (⟨j.1, fresh j.2⟩ : ResidualVertex h) := Subtype.ext hvj
    simpa only [hui', hvj'] using hij
  have huv := ForestCentroid.componentBatch_separated (residualGraph G h) pick u v hu hv he
  apply Subtype.ext
  exact hui.symm.trans ((congrArg Subtype.val huv).trans hvj)

omit [Nonempty V] in
/-- In a correct residual forest, the implemented terminal action selects
a genuine centroid batch and is structurally safe. -/
theorem terminalBatch_safe (M : ForestModel N V) (G : SimpleGraph (Position N)) (h : History N V)
    (heq : residualGraph G h = residualGraph M.graph h) (hres : h.uncommitted.Nonempty) :
    M.BatchStructurallySafe h (CappedController.terminalBatch h G hres).batch
      (CappedController.terminalBatch h G hres).fresh := by
  have hforest : (residualGraph G h).IsAcyclic := heq ▸ M.graph_acyclic.induce _
  unfold CappedController.terminalBatch
  simp only [dif_pos hforest]
  exact componentBatch_safe M G h heq _ _

omit [Fintype V] [Nonempty V] in
/-- Every actual component after the implemented centroid batch is at most
half its actual previous parent component. -/
theorem terminalBatch_halves (G : SimpleGraph (Position N)) (h : History N V)
    (hforest : (residualGraph G h).IsAcyclic) (hres : h.uncommitted.Nonempty)
    (z : (CappedController.terminalBatch h G hres).batch → V)
    (C : (residualGraph G (h.appendBatch (CappedController.terminalBatch h G hres).batch
      (CappedController.terminalBatch h G hres).fresh z)).ConnectedComponent) :
    2 * Nat.card C ≤ Nat.card (C.map (appendEmbedding G h
      (CappedController.terminalBatch h G hres).batch
      (CappedController.terminalBatch h G hres).fresh z).toHom) := by
  apply ForestIteration.component_halves_of_embedding _
    (CappedController.smallestCentroid (residualGraph G h) hforest)
    (CappedController.smallestCentroid_spec _ hforest)
  intro v hv
  have horig : v.1 ∈ (CappedController.terminalBatch h G hres).batch := by
    simp only [CappedController.terminalBatch, dif_pos hforest]
    exact Finset.mem_map.mpr ⟨appendEmbedding G h _ _ z v, hv, rfl⟩
  have hnot : v.1 ∈ h.uncommitted \ (CappedController.terminalBatch h G hres).batch := by
    simpa only [History.appendBatch_uncommitted] using v.2
  exact (Finset.mem_sdiff.mp hnot).2 horig

omit [Fintype V] [Nonempty V] in
/-- An integral component-size bound strictly below one certifies completion
of the actual history. -/
theorem complete_of_components_lt_one (G : SimpleGraph (Position N)) (h : History N V)
    (hbound : ∀ C : (residualGraph G h).ConnectedComponent, Nat.card C < 1) :
    h.committed = Finset.univ := by
  by_contra hc
  obtain ⟨v, hv⟩ := h.uncommitted_nonempty_of_not_complete hc
  let w : ResidualVertex h := ⟨v, hv⟩
  let C := (residualGraph G h).connectedComponentMk w
  let : Nonempty C := ⟨⟨w, rfl⟩⟩
  have hp : 0 < Nat.card C := Nat.card_pos
  have hb := hbound C
  omega

omit [Nonempty V] in
/-- With a correct public residual graph and enough centroid fuel, the
actual terminal program uses only structurally safe centroid commits.
The zero-fuel hard guard is unreachable before completion. -/
theorem terminal_structurallySafe (M : ForestModel N V) (O : FrozenOracle N V)
    (G : SimpleGraph (Position N)) (extra : ℕ) (h : History N V)
    (heq : residualGraph G h = residualGraph M.graph h)
    (hbound : ∀ C : (residualGraph G h).ConnectedComponent, Nat.card C < 2 ^ extra) :
    Program.StructurallySafe M O (CappedController.terminal extra h G) := by
  induction extra generalizing h with
  | zero =>
      have hc := complete_of_components_lt_one G h (by simpa using hbound)
      simp [CappedController.terminal, hc, Program.StructurallySafe]
  | succ extra ih =>
      rw [CappedController.terminal]
      split
      · trivial
      · rename_i hc
        change M.BatchStructurallySafe h _ _ ∧ ∀ z,
          Program.StructurallySafe M O (CappedController.terminal extra _ G)
        constructor
        · exact terminalBatch_safe M G h heq _
        · intro z
          apply ih _ (residual_eq_append G M.graph h heq _ _ z)
          intro C
          have hh := terminalBatch_halves G h (heq ▸ M.graph_acyclic.induce _) _ z C
          have hp := hbound (C.map (appendEmbedding G h _ _ z).toHom)
          have hlt := hh.trans_lt hp
          rw [pow_succ] at hlt
          omega

omit [Nonempty V] in
/-- The exact public logarithmic depth supplies enough fuel to the concrete
terminal controller from every history, independently of residual sizes. -/
theorem terminal_structurallySafe_of_depth (M : ForestModel N V) (O : FrozenOracle N V)
    (G : SimpleGraph (Position N)) (extra : ℕ) (h : History N V)
    (heq : residualGraph G h = residualGraph M.graph h)
    (hextra : ForestIteration.centroidDepth N ≤ extra) :
    Program.StructurallySafe M O (CappedController.terminal extra h G) := by
  apply terminal_structurallySafe M O G extra h heq
  intro C
  have hcard : Nat.card C ≤ N := by
    have hi := Nat.card_le_card_of_injective (fun x : C ↦ x.1.1)
      (fun x y hxy ↦ Subtype.ext (Subtype.ext hxy))
    simpa using hi
  exact hcard.trans_lt ((ForestIteration.lt_two_pow_centroidDepth N).trans_le
    (Nat.pow_le_pow_right (by decide) hextra))

end
end ForestSampling.PackedStructure
