import ForestSampling.PairConditionals
import ForestSampling.FiniteInformation

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
noncomputable section

namespace FinDist

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two independent Boolean-indexed coordinates have their ordinary
product law after the explicit coordinate-pair equivalence. -/
theorem piProduct_bool_map_pair (laws : Bool → FinDist V) :
    (piProduct laws).map (Equiv.boolArrowEquivProd V) = (laws false).prod (laws true) := by
  ext ab
  rw [map_equiv_apply, piProduct_apply, prod_apply]
  simp [Equiv.boolArrowEquivProd, mul_comm]

end FinDist

namespace MaskedState

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The observed entries of a masked state form a committed history for
conditional-law calculations; this does not change a sampling transcript. -/
def toHistory (y : MaskedState N V) : History N V where
  committed := y.observed
  value i := Classical.choose ((y.mem_observed_iff i).mp i.2)

theorem toHistory_value (y : MaskedState N V) (i : y.toHistory.committed) :
    y i = some (y.toHistory.value i) :=
  Classical.choose_spec ((y.mem_observed_iff i).mp i.2)

theorem agrees_toHistory_iff (y : MaskedState N V) (x : Configuration N V) :
    y.toHistory.Agrees x ↔ y.Agrees x := by
  constructor
  · intro hh k a hka
    have hk : k ∈ y.toHistory.committed := (y.mem_observed_iff k).mpr ⟨a, hka⟩
    have he := y.toHistory_value ⟨k,hk⟩
    rw [hka] at he
    exact (hh ⟨k,hk⟩).trans (Option.some.inj he).symm
  · intro hh i
    exact hh i _ (y.toHistory_value i)

@[simp] theorem mem_toHistory_uncommitted (y : MaskedState N V) (i : Position N) :
    i ∈ y.toHistory.uncommitted ↔ y i = none := by
  rw [History.mem_uncommitted_iff]
  change i ∉ y.observed ↔ y i = none
  rw [mem_observed_iff_ne_none]
  simp

/-- The actual observed-history pair is the two-coordinate readout of
the actual residual conditional law. -/
theorem exactPair_eq_residual_map (M : ForestModel N V) (y : MaskedState N V)
    (i j : Position N) (hi : y i = none) (hj : y j = none) :
    y.exactPair M.target M.target_positive i j =
      (y.toHistory.residualLaw M.target M.target_positive).map
        (fun x ↦ (x ⟨i, (y.mem_toHistory_uncommitted i).mpr hi⟩,
          x ⟨j, (y.mem_toHistory_uncommitted j).mpr hj⟩)) := by
  unfold exactPair History.residualLaw
  simp only [FinDist.conditionalMap, FinDist.map_comp]
  apply FinDist.conditionalMap_congr M.target y.Agrees y.toHistory.Agrees
    (y.probability_pos M.target M.target_positive)
    (y.toHistory.probability_pos M.target M.target_positive)
    (fun x ↦ (x i,x j)) (fun x ↦ (x i,x j))
    (fun x ↦ (y.agrees_toHistory_iff x).symm) (fun _ ↦ rfl)

/-- Vertices in distinct residual blocks are conditionally independent
under every observed history; the forest factorization proves the block
independence rather than imposing it as a new assumption. -/
theorem exactPair_prod_of_separated_labels {C : Type*} [Fintype C] [DecidableEq C]
    (M : ForestModel N V) (y : MaskedState N V)
    (label : ResidualVertex y.toHistory → C)
    (hseparated : ∀ u v : ResidualVertex y.toHistory,
      M.graph.Adj u.1 v.1 → label u = label v)
    (i j : Position N) (hi : y i = none) (hj : y j = none)
    (hne : label ⟨i, (y.mem_toHistory_uncommitted i).mpr hi⟩ ≠
      label ⟨j, (y.mem_toHistory_uncommitted j).mpr hj⟩) :
    ∃ p q : FinDist V, y.exactPair M.target M.target_positive i j = p.prod q := by
  classical
  let u : ResidualVertex y.toHistory := ⟨i, (y.mem_toHistory_uncommitted i).mpr hi⟩
  let v : ResidualVertex y.toHistory := ⟨j, (y.mem_toHistory_uncommitted j).mpr hj⟩
  let vertex : Bool → ResidualVertex y.toHistory := fun b ↦ if b then v else u
  let select : Bool → Option C := fun b ↦ some (label (vertex b))
  obtain ⟨laws, hlaws⟩ := M.residualLaw_factorizes_over_blocks y.toHistory label hseparated
  let readout : (b : Bool) → ({a : ResidualVertex y.toHistory // some (label a) = select b} → V) → V :=
    fun b z ↦ z ⟨vertex b, rfl⟩
  have hselect : Function.Injective select := by
    intro a b hab
    cases a <;> cases b <;> simp_all [select, vertex, u, v]
  have hh := FinDist.piProduct_map_distinct_blocks laws select hselect readout
  refine ⟨(laws (select false)).map (readout false), (laws (select true)).map (readout true), ?_⟩
  rw [← FinDist.piProduct_bool_map_pair (fun b ↦ (laws (select b)).map (readout b)), ← hh, FinDist.map_comp, ← hlaws, FinDist.map_comp,
    exactPair_eq_residual_map M y i j hi hj]
  congr 1

/-- The separated actual pair's mutual information vanishes exactly. -/
theorem exactPair_mutualInformation_eq_zero_of_separated_labels
    {C : Type*} [Fintype C] [DecidableEq C]
    (M : ForestModel N V) (y : MaskedState N V)
    (label : ResidualVertex y.toHistory → C)
    (hseparated : ∀ u v : ResidualVertex y.toHistory,
      M.graph.Adj u.1 v.1 → label u = label v)
    (i j : Position N) (hi : y i = none) (hj : y j = none)
    (hne : label ⟨i, (y.mem_toHistory_uncommitted i).mpr hi⟩ ≠
      label ⟨j, (y.mem_toHistory_uncommitted j).mpr hj⟩) :
    (y.exactPair M.target M.target_positive i j).mutualInformation = 0 := by
  obtain ⟨p,q,h⟩ := exactPair_prod_of_separated_labels M y label hseparated i j hi hj hne
  rw [h, FinDist.mutualInformation_prod]

end MaskedState
end
end ForestSampling
