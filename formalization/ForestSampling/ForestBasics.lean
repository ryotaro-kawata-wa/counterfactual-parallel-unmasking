import ForestSampling.ForestPeeling
import ForestSampling.ForestCentroid

set_option autoImplicit false
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ForestSampling.ForestBasics

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Decomposing vertices by their actual connected component is a bijection. -/
noncomputable def componentVerticesEquiv (G : SimpleGraph A) :
    (Σ C : G.ConnectedComponent, C) ≃ A where
  toFun v := v.2.val
  invFun v := ⟨G.connectedComponentMk v, ⟨v, rfl⟩⟩
  left_inv := by
    rintro ⟨C, v, hv⟩
    cases hv
    rfl
  right_inv _ := rfl

/-- Restriction to a whole connected component preserves every degree. -/
theorem component_degree (G : SimpleGraph A) [DecidableRel G.Adj]
    (C : G.ConnectedComponent) (v : C) : C.toSimpleGraph.degree v = G.degree v := by
  classical
  have hsub : G.neighborSet v.val ⊆ C.supp := by
    intro w hw
    exact (SimpleGraph.ConnectedComponent.sound hw.reachable).symm.trans v.2
  have hm : (C.toSimpleGraph.neighborFinset v).map (Function.Embedding.subtype _) =
      G.neighborFinset v.val := by
    ext w
    constructor
    · intro hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hw
      exact (G.mem_neighborFinset _ _).mpr ((C.toSimpleGraph.mem_neighborFinset _ _).mp hu)
    · intro hw
      have ha := (G.mem_neighborFinset _ _).mp hw
      exact Finset.mem_map.mpr ⟨⟨w, hsub ha⟩, (C.toSimpleGraph.mem_neighborFinset _ _).mpr ha, rfl⟩
  calc
    _ = (C.toSimpleGraph.neighborFinset v).card := rfl
    _ = ((C.toSimpleGraph.neighborFinset v).map (Function.Embedding.subtype _)).card :=
      (Finset.card_map _).symm
    _ = (G.neighborFinset v.val).card := congrArg Finset.card hm
    _ = _ := rfl

/-- Exact finite forest Euler count, including the empty graph. -/
theorem edge_card_add_components (G : SimpleGraph A) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) : G.edgeFinset.card + Nat.card G.ConnectedComponent = Fintype.card A := by
  classical
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have hlocal : ∀ C : G.ConnectedComponent,
      (∑ v : C, C.toSimpleGraph.degree v) + 2 = 2 * Fintype.card C := by
    intro C
    have ht := hG.isTree_connectedComponent C
    have he := ht.card_edgeFinset
    have hd := C.toSimpleGraph.sum_degrees_eq_twice_card_edges
    omega
  have hsum := congrArg (fun f : G.ConnectedComponent → ℕ ↦ ∑ C, f C) (funext hlocal)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have hdegrees : (∑ C : G.ConnectedComponent, ∑ v : C, C.toSimpleGraph.degree v) =
      ∑ v : A, G.degree v := by
    simp_rw [component_degree]
    calc
      _ = ∑ p : (Σ C : G.ConnectedComponent, C), G.degree p.2.val :=
        (Fintype.sum_sigma (fun p : (Σ C : G.ConnectedComponent, C) ↦ G.degree p.2.val)).symm
      _ = _ := Fintype.sum_equiv (componentVerticesEquiv G) _ _ (fun _ ↦ rfl)
  have hcard : (∑ C : G.ConnectedComponent, Fintype.card C) = Fintype.card A := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (componentVerticesEquiv G)
  rw [hdegrees, hcard, G.sum_degrees_eq_twice_card_edges] at hsum
  rw [Nat.card_eq_fintype_card]
  norm_num only [Nat.cast_id] at hsum
  omega

/-- The edge count is the number of vertices minus the number of actual
components, in the precise form used by the manuscript. -/
theorem edge_card_eq_vertices_sub_components (G : SimpleGraph A) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) :
    G.edgeFinset.card = Fintype.card A - Nat.card G.ConnectedComponent := by
  have hh := edge_card_add_components G hG
  omega

/-- Package the finite nonempty forest count and degree-sum assertions. -/
theorem forest_counts (G : SimpleGraph A) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) [Nonempty A] :
    G.edgeFinset.card = Fintype.card A - Nat.card G.ConnectedComponent ∧
    (∑ v, G.degree v) = 2 * G.edgeFinset.card ∧
    (∑ v, G.degree v) < 2 * Fintype.card A :=
  ⟨edge_card_eq_vertices_sub_components G hG, G.sum_degrees_eq_twice_card_edges,
    ForestPeeling.degree_sum_lt_twice_card G hG⟩

end ForestSampling.ForestBasics
