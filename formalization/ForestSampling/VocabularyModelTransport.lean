import ForestSampling.VocabularyEquivalence
import ForestSampling.PublicClassLower
import ForestSampling.KLOracle

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace VocabularyEquivalence
universe u v
variable {N : ℕ} {V : Type u} {W : Type v}
variable [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- Exact coordinate marginals commute with a public token relabeling. -/
theorem positionMarginal_map (e : V ≃ W) (p : FinDist (Configuration N V)) (i : Position N) :
    (p.map (configuration e)).positionMarginal i = (p.positionMarginal i).map e := by
  unfold FinDist.positionMarginal
  rw [FinDist.map_comp, FinDist.map_comp]
  rfl

/-- Relabel the actual target and edge kernels while keeping its hidden
forest and rooting fixed. All model certificates are transported explicitly. -/
noncomputable def model (e : V ≃ W) (M : ForestModel N V) : ForestModel N W where
  target := M.target.map (configuration e)
  target_positive := M.target.map_strictlyPositive_of_surjective M.target_positive
    (configuration e) (configuration e).surjective
  graph := M.graph
  graph_acyclic := M.graph_acyclic
  kernel i j b := (M.kernel i j (e.symm b)).map e
  kernel_positive := fun {_ _} hij b ↦ FinDist.map_strictlyPositive_of_surjective _
    (M.kernel_positive hij (e.symm b)) e e.surjective
  rooting := M.rooting
  factorizes := by
    intro x
    unfold ForestFactorization.mass
    simp_rw [positionMarginal_map, FinDist.map_equiv_apply]
    exact M.factorizes ((configuration e).symm x)
  endpoint_compatible := by
    intro i j hij a b
    simp only [positionMarginal_map, FinDist.map_equiv_apply]
    exact M.endpoint_compatible hij (e.symm a) (e.symm b)

@[simp] theorem model_target (e : V ≃ W) (M : ForestModel N V) :
    (model e M).target = M.target.map (configuration e) := rfl

@[simp] theorem model_graph (e : V ≃ W) (M : ForestModel N V) : (model e M).graph = M.graph := rfl

@[simp] theorem model_marginal (e : V ≃ W) (M : ForestModel N V) (i : Position N) :
    (model e M).marginal i = (M.marginal i).map e := positionMarginal_map e M.target i

/-- The finite complete-boundary conditional itself is transported, not
only a scalar response estimate. -/
theorem model_boundaryRow (e : V ≃ W) (M : ForestModel N V)
    (i j : Position N) (a : V) (z : CompleteBoundary N V i j) :
    (model e M).target.boundaryRow (model e M).target_positive i j (e a) (fun k ↦ e (z k)) =
      (M.target.boundaryRow M.target_positive i j a z).map e := by
  classical
  let E := CompleteBoundary.Event i j (e a) (fun k ↦ e (z k))
  have he : E ∘ configuration e = CompleteBoundary.Event i j a z := by
    funext x
    apply propext
    simp only [E, CompleteBoundary.Event, Function.comp_apply, configuration_apply,
      Equiv.apply_eq_iff_eq]
  have hpos : 0 < M.target.eventMass (E ∘ configuration e) := by
    rw [M.target.eventMass_congr (E ∘ configuration e) (CompleteBoundary.Event i j a z)
      (fun x ↦ Iff.of_eq (congrFun he x))]
    exact M.target.boundaryEventMass_pos M.target_positive i j a z
  unfold FinDist.boundaryRow
  change (M.target.map (configuration e)).conditionalMap E _ (fun x ↦ x j) = _
  rw [FinDist.map_equiv_conditionalMap M.target (configuration e) E hpos]
  calc
    _ = M.target.conditionalMap (CompleteBoundary.Event i j a z)
        (M.target.boundaryEventMass_pos M.target_positive i j a z) (fun x ↦ e (x j)) :=
      M.target.conditionalMap_congr _ _ _ _ _ _
        (fun x ↦ Iff.of_eq (congrFun he x)) (fun _ ↦ rfl)
    _ = _ := by unfold FinDist.conditionalMap; rw [FinDist.map_comp]; rfl

/-- The exact marginal tail is carried by the same token bijection. -/
theorem mem_model_tailSet (e : V ≃ W) (M : ForestModel N V) (i : Position N) (t : ℝ) (a : V) :
    e a ∈ (model e M).tailSet i t ↔ a ∈ M.tailSet i t := by
  simp [ForestModel.mem_tailSet_iff, model_marginal, FinDist.map_equiv_apply]

/-- RT holds with exactly the same constants after any public renaming. -/
theorem model_tailResponseRegular (e : V ≃ W) (M : ForestModel N V) (C s : ℝ)
    (h : M.TailResponseRegular C s) : (model e M).TailResponseRegular C s := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro i j hij t ht0 ht1 z a b ha hb
  let z' : CompleteBoundary N V i j := fun k ↦ e.symm (z k)
  have hz : (fun k ↦ e (z' k)) = z := by funext k; simp [z']
  have hr := h.2.2 i j hij t ht0 ht1 z' (e.symm a) (e.symm b)
    ((mem_model_tailSet e M i t (e.symm a)).mp (by simpa using ha))
    ((mem_model_tailSet e M i t (e.symm b)).mp (by simpa using hb))
  have hrow (c : W) := model_boundaryRow e M i j (e.symm c) z'
  simp only [Equiv.apply_symm_apply, hz] at hrow
  rw [hrow a, hrow b, FinDist.tv_map_equiv]
  exact hr

/-- Both directed responses, and therefore their uniform lower signal,
are preserved by token relabeling. -/
theorem model_edgeNondegenerate [Nonempty V] [Nonempty W]
    (e : V ≃ W) (M : ForestModel N V) (signal : ℝ)
    (h : M.EdgeNondegenerate signal) : (model e M).EdgeNondegenerate signal := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro i j hij z
  let z' : CompleteBoundary N V i j := fun k ↦ e.symm (z k)
  have hz : (fun k ↦ e (z' k)) = z := by funext k; simp [z']
  apply (h.2.2 hij z').trans
  apply Finset.sup'_le
  intro ab _
  have hr := (model e M).pair_response_le_directedResponse hij.ne z (e ab.1) (e ab.2)
  have hrow (a : V) := model_boundaryRow e M i j a z'
  rw [hz] at hrow
  rw [hrow ab.1, hrow ab.2, FinDist.tv_map_equiv] at hr
  exact hr

/-- Exact-mass rank order is carried over; the finite rank indices use
only the cardinality equality induced by the public token bijection. -/
noncomputable def ranking (e : V ≃ W) (M : ForestModel N V) (r : MarginalRanking M) :
    MarginalRanking (model e M) where
  token i k := e (r.token i (Fin.cast (Fintype.card_congr e).symm k))
  token_bijective i := e.bijective.comp ((r.token_bijective i).comp
    (finCongr (Fintype.card_congr e).symm).bijective)
  nonincreasing i k l hkl := by
    simp only [model_marginal, FinDist.map_equiv_apply, Equiv.symm_apply_apply]
    exact r.nonincreasing i _ _ hkl

theorem model_finiteRankFrequency (e : V ≃ W) (M : ForestModel N V) (r : MarginalRanking M)
    (exponent constant : ℝ) (h : FiniteRankFrequency M r exponent constant) :
    FiniteRankFrequency (model e M) (ranking e M r) exponent constant := by
  intro i k
  have hh := h i (Fin.cast (Fintype.card_congr e).symm k)
  simpa only [ranking, model_marginal, FinDist.map_equiv_apply, Equiv.symm_apply_apply,
    Fin.val_cast, Fintype.card_congr e] using hh

/-- Agreement with observed values is unchanged by relabeling both a
masked state and a complete configuration. -/
theorem agrees_state (e : V ≃ W) (y : MaskedState N V) (x : Configuration N V) :
    (state e y).Agrees (configuration e x) ↔ y.Agrees x := by
  constructor
  · intro h i a hi
    apply e.injective
    exact h i (e a) (by simp [state, hi])
  · intro h i b hib
    cases hi : y i with
    | none => simp [state, hi] at hib
    | some a =>
        have hb : e a = b := by simpa [state, hi] using hib
        rw [← hb]
        change e (x i) = e a
        rw [h i a hi]

/-- Every actual masked-state conditional is the pushforward of its
pullback-state conditional. This includes all counterfactual query states. -/
theorem model_exactRow_pull [Nonempty V] [Nonempty W]
    (e : V ≃ W) (M : ForestModel N V) (y : MaskedState N W) (j : MaskedPosition y) :
    y.exactRow (model e M).target (model e M).target_positive j =
      ((state e.symm y).exactRow M.target M.target_positive (maskedPosition e.symm y j)).map e := by
  classical
  have he : y.Agrees ∘ configuration e = (state e.symm y).Agrees := by
    funext x
    apply propext
    have hh := agrees_state e.symm y (configuration e x)
    have hc : configuration e.symm (configuration e x) = x := by funext i; simp
    rw [hc] at hh
    exact hh.symm
  have hpos : 0 < M.target.eventMass (y.Agrees ∘ configuration e) := by
    rw [M.target.eventMass_congr (y.Agrees ∘ configuration e) (state e.symm y).Agrees
      (fun x ↦ Iff.of_eq (congrFun he x))]
    exact (state e.symm y).probability_pos M.target M.target_positive
  unfold MaskedState.exactRow
  change (M.target.map (configuration e)).conditionalMap y.Agrees _ (fun x ↦ x j.1) = _
  rw [FinDist.map_equiv_conditionalMap M.target (configuration e) y.Agrees hpos]
  calc
    _ = M.target.conditionalMap (state e.symm y).Agrees
        ((state e.symm y).probability_pos M.target M.target_positive) (fun x ↦ e (x j.1)) :=
      M.target.conditionalMap_congr _ _ _ _ _ _
        (fun x ↦ Iff.of_eq (congrFun he x)) (fun _ ↦ rfl)
    _ = _ := by unfold FinDist.conditionalMap; rw [FinDist.map_comp]; rfl

/-- Uniform squared-Hellinger accuracy is invariant for the complete
transported frozen map, including the manuscript's exact normalization. -/
theorem oracle_accurate [Nonempty V] [Nonempty W]
    (e : V ≃ W) (M : ForestModel N V) (O : FrozenOracle N V) (radius : ℝ)
    (h : O.Accurate M radius) : (oracle e O).Accurate (model e M) radius := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro y j
  rw [model_exactRow_pull, oracle_row, FinDist.sqHellinger_map_equiv]
  exact h.2.2 _ _

/-- Forward-KL accuracy is invariant with its direction unchanged. -/
theorem oracle_forwardKLAccurate [Nonempty V] [Nonempty W]
    (e : V ≃ W) (M : ForestModel N V) (O : FrozenOracle N V) (κ : ℝ)
    (h : O.ForwardKLAccurate M κ) : (oracle e O).ForwardKLAccurate (model e M) κ := by
  refine ⟨h.1, ?_⟩
  intro y j
  rw [model_exactRow_pull, oracle_row, FinDist.klDivergence_map_equiv]
  exact h.2 _ _

/-- A target and its one fixed oracle are transported together. -/
noncomputable def samplingInstance (e : V ≃ W) (I : SamplingInstance N V) : SamplingInstance N W :=
  ⟨model e I.model, oracle e I.oracle⟩

/-- Membership in the whole public Hellinger class is preserved under a
public renaming; no hidden ranking or model data are given to the sampler. -/
theorem publicClass [Nonempty V] [Nonempty W] (e : V ≃ W) (I : SamplingInstance N V)
    (exponent signal radius : ℝ) (h : HellingerPublicClass exponent signal radius I) :
    HellingerPublicClass exponent signal radius (samplingInstance e I) := by
  obtain ⟨he, hRT, hUEN, ⟨r, hRF⟩, hO⟩ := h
  exact ⟨he, model_tailResponseRegular e I.model 1 1 hRT,
    model_edgeNondegenerate e I.model signal hUEN,
    ⟨ranking e I.model r, model_finiteRankFrequency e I.model r exponent 1 hRF⟩,
    oracle_accurate e I.model I.oracle radius hO⟩

end VocabularyEquivalence
end ForestSampling
