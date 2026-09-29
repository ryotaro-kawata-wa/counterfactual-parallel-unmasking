import ForestSampling.ScreenExecution
import ForestSampling.ScreeningSelector
import ForestSampling.ForestPeeling
import ForestSampling.ForestCentroid

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace History

variable {N : ℕ} {V : Type*} [DecidableEq V]

theorem uncommitted_nonempty_of_not_complete (h : History N V)
    (hc : h.committed ≠ Finset.univ) : h.uncommitted.Nonempty := by
  by_contra hnone
  have hempty := Finset.not_nonempty_iff_eq_empty.mp hnone
  apply hc
  ext i
  have hi : i ∉ h.uncommitted := by simp [hempty]
  simpa using hi

theorem append_all_complete (h : History N V) (z : h.uncommitted → V) :
    (h.appendBatch h.uncommitted (fun _ hi ↦ hi) z).committed = Finset.univ := by
  rw [History.appendBatch_committed]
  ext i
  simp [History.uncommitted]

end History

/-- A concrete nonempty fresh commit batch selected using public state. -/
structure FreshBatch {N : ℕ} {V : Type*} [DecidableEq V] (h : History N V) where
  batch : Finset (Position N)
  nonempty : batch.Nonempty
  fresh : batch ⊆ h.uncommitted

namespace Program

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The hard guard commits every remaining position in one final batch.
It is available on arbitrary failed-screen paths and always terminates. -/
noncomputable def commitAll (h : History N V) : Program N V h :=
  if hc : h.committed = Finset.univ then .done hc else
    .commit h.uncommitted (h.uncommitted_nonempty_of_not_complete hc) (fun _ hi ↦ hi)
      (fun z ↦ .done (h.append_all_complete z))

theorem commitAll_withinBudgets (h : History N V) (Q : ℕ) :
    WithinBudgets (commitAll h) Q 1 := by
  unfold commitAll
  split
  · trivial
  · exact ⟨by decide, fun _ ↦ True.intro⟩

end Program

namespace CappedController

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The public graph formed from the final selected directed rows, with
the manuscript's undirected union and no self-loops. -/
noncomputable def rowGraph (h : History N V)
    (rows : ResidualVertex h → Finset (ResidualVertex h)) : SimpleGraph (Position N) :=
  SimpleGraph.fromRel (fun i j ↦ ∃ hi : i ∈ h.uncommitted, ∃ hj : j ∈ h.uncommitted,
    (⟨j, hj⟩ : ResidualVertex h) ∈ rows ⟨i, hi⟩)

/-- The smallest public-label centroid in a connected component. -/
noncomputable def smallestCentroid {A : Type*} [Fintype A] [LinearOrder A]
    (G : SimpleGraph A) (hG : G.IsAcyclic) (C : G.ConnectedComponent) : C := by
  classical
  let candidates : Finset C := Finset.univ.filter (ForestCentroid.IsCentroid C.toSimpleGraph)
  have hnonempty : candidates.Nonempty := by
    obtain ⟨v, hv⟩ := ForestCentroid.exists_centroid C.toSimpleGraph (hG.isTree_connectedComponent C)
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
  exact candidates.min' hnonempty

theorem smallestCentroid_spec {A : Type*} [Fintype A] [LinearOrder A]
    (G : SimpleGraph A) (hG : G.IsAcyclic) (C : G.ConnectedComponent) :
    ForestCentroid.IsCentroid C.toSimpleGraph (smallestCentroid G hG C) := by
  classical
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).2

/-- Vertices lying on a current public-graph cycle. -/
noncomputable def cycleVertices {A : Type*} [Fintype A] (G : SimpleGraph A) : Finset A := by
  classical
  exact Finset.univ.filter (fun v ↦ ∃ p : G.Walk v v, p.IsCycle)

theorem cycleVertices_nonempty {A : Type*} [Fintype A] (G : SimpleGraph A)
    (hG : ¬ G.IsAcyclic) : (cycleVertices G).Nonempty := by
  classical
  by_contra hn
  apply hG
  intro v p hp
  exact hn ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p, hp⟩⟩⟩

/-- Choose a maximum-degree cycle vertex and break ties by public label. -/
noncomputable def cycleVertex {A : Type*} [Fintype A] [LinearOrder A]
    (G : SimpleGraph A) (hG : ¬ G.IsAcyclic) : A := by
  classical
  let cycle := cycleVertices G
  let maxDegree := cycle.sup (fun v ↦ G.degree v)
  let candidates := cycle.filter (fun v ↦ G.degree v = maxDegree)
  have hnonempty : candidates.Nonempty := by
    obtain ⟨v, hv, heq⟩ := Finset.exists_mem_eq_sup cycle (cycleVertices_nonempty G hG) (fun v ↦ G.degree v)
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, heq.symm⟩⟩
  exact candidates.min' hnonempty

/-- One actual terminal action: delete a maximum-degree cycle vertex until
the public graph is a forest, then commit one centroid per component. -/
noncomputable def terminalBatch (h : History N V) (G : SimpleGraph (Position N))
    (hres : h.uncommitted.Nonempty) : FreshBatch h := by
  classical
  let H := residualGraph G h
  let _ : Nonempty (ResidualVertex h) := ⟨⟨hres.choose, hres.choose_spec⟩⟩
  by_cases hH : H.IsAcyclic
  · let batch := ForestCentroid.componentBatch H (smallestCentroid H hH)
    refine ⟨batch.map (Function.Embedding.subtype _), ?_, ?_⟩
    · exact (ForestCentroid.componentBatch_nonempty H _).map
    · intro j hj
      obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hj
      exact v.property
  · let v := cycleVertex H hH
    exact ⟨{v.val}, Finset.singleton_nonempty _,
      by intro j hj; simpa only [Finset.mem_singleton.mp hj] using v.property⟩

/-- Terminal execution with one reserved final round. Zero extra fuel
activates the hard fallback; each ordinary terminal commit consumes one
extra round, so arbitrary erroneous public graphs still terminate. -/
noncomputable def terminal : ℕ → (h : History N V) → SimpleGraph (Position N) → Program N V h
  | extra, h, G =>
      if hc : h.committed = Finset.univ then .done hc else
        match extra with
        | 0 => Program.commitAll h
        | extra' + 1 =>
            let B := terminalBatch h G (h.uncommitted_nonempty_of_not_complete hc)
            .commit B.batch B.nonempty B.fresh
              (fun z ↦ terminal extra' (h.appendBatch B.batch B.fresh z) G)

/-- The terminal controller's hard round cap is valid on every possible
commit outcome, without any assertion that the public graph is correct. -/
theorem terminal_withinBudgets (extra : ℕ) (h : History N V)
    (G : SimpleGraph (Position N)) (Q : ℕ) :
    Program.WithinBudgets (terminal extra h G) Q (extra + 1) := by
  induction extra generalizing h with
  | zero =>
      unfold terminal
      split
      · trivial
      · exact Program.commitAll_withinBudgets h Q
  | succ extra ih =>
      unfold terminal
      split
      · trivial
      · constructor
        · omega
        · intro z
          simpa using ih _

/-- Commit a frozen public peel list in order. Each ordinary singleton
uses one extra round; the reserved last round commits all remaining
positions. The continuation receives only the remaining fuel and history. -/
noncomputable def peelPass : List (Position N) → ℕ → (h : History N V) →
    ((extra : ℕ) → (h : History N V) → Program N V h) → Program N V h
  | [], extra, h, after => after extra h
  | j :: todo, extra, h, after =>
      if hc : h.committed = Finset.univ then .done hc else
        if hj : j ∈ h.uncommitted then
          match extra with
          | 0 => Program.commitAll h
          | extra' + 1 =>
              .commit {j} (Finset.singleton_nonempty _) (by simpa using hj)
                (fun z ↦ peelPass todo extra' (h.appendBatch {j} (by simpa using hj) z) after)
        else peelPass todo extra h after

/-- Frozen-list peeling preserves both universal resource allowances. -/
theorem peelPass_withinBudgets (todo : List (Position N)) (extra : ℕ) (h : History N V)
    (after : (extra : ℕ) → (h : History N V) → Program N V h) (Q : ℕ)
    (hafter : ∀ extra h, Program.WithinBudgets (after extra h) Q (extra + 1)) :
    Program.WithinBudgets (peelPass todo extra h after) Q (extra + 1) := by
  induction todo generalizing extra h with
  | nil => exact hafter extra h
  | cons j todo ih =>
      rw [peelPass]
      split
      · trivial
      · split
        · cases extra with
          | zero => exact Program.commitAll_withinBudgets h Q
          | succ extra =>
              constructor
              · omega
              · intro z
                simpa using ih extra _
        · exact ih extra h

end CappedController
end ForestSampling
