import ForestSampling.ScreeningAggregate
import ForestSampling.ScreenColorProbability

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace Screening

noncomputable section
attribute [local instance] Classical.propDecidable

variable {N : ℕ} {V Color : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable [Fintype Color] [DecidableEq Color] [Nonempty Color]

omit [Nonempty V] in
/-- The neighbor count in the probability calculation is the actual
neighbor-row cardinality in the deterministic screen contract. -/
theorem card_ResidualNeighbors (M : ForestModel N V) (h : History N V)
    (j : ResidualVertex h) :
    Fintype.card (ResidualNeighbors M h j) = (residualNeighbors M h j).card := by
  simp only [ResidualNeighbors, Fintype.card_subtype, residualNeighbors, M.graph.adj_comm]

omit [Nonempty V] [Fintype Color] [DecidableEq Color] [Nonempty Color] in
/-- Failure of a strict separating majority is the bad-count event used by
the independent-color concentration proof, including majority ties. -/
theorem screenSuccess_of_not_somePairFails (M : ForestModel N V) (h : History N V)
    (D T : ℕ) (colors : Fin T → Position N → Color)
    (hgood : ¬ SomePairFails M h D T colors) : ScreenSuccess M h colors D := by
  intro i j _ hdegree
  have hnot : ¬ T ≤ 2 * FinDist.badCount (fun _ color ↦ ¬ Separating M h color i j) colors := by
    intro hbad
    exact hgood ⟨i, j, by rwa [card_ResidualNeighbors], hbad⟩
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun τ : Fin T ↦ Separating M h (colors τ) i j)
  have hbadEq : FinDist.badCount (fun _ color ↦ ¬ Separating M h color i j) colors =
      (Finset.univ.filter (fun τ : Fin T ↦ ¬ Separating M h (colors τ) i j)).card := by
    simp [FinDist.badCount, Finset.card_filter]
  rw [hbadEq] at hnot
  simp only [Finset.card_univ, Fintype.card_fin] at hpartition ⊢
  omega

/-- At a fixed pre-color history, the exact screen-success event has the
manuscript's allocated failure probability under fresh independent colors. -/
theorem screenFailure_le_budget (M : ForestModel N V) (h : History N V)
    (D T S : ℕ) (η : ℝ) (hN : 0 < N) (hS : 0 < S) (hη : 0 < η)
    (hcolors : 8 * (D + 1) ≤ Fintype.card Color)
    (hT : 8 * Real.log ((S : ℝ) * (N : ℝ)^2 / η) ≤ (T : ℝ)) :
    (FinDist.piProduct fun _ : Fin T ↦
      FinDist.uniformColors (α := Position N) (Color := Color)).eventMass
      (fun colors ↦ ¬ ScreenSuccess M h colors D) ≤ η / S := by
  apply (FinDist.eventMass_mono _ _ (SomePairFails M h D T) ?_).trans
    (somePairFails_le_budget M h D T S η hN hS hη hcolors hT)
  intro colors hfail
  exact not_not.mp (fun hgood ↦ hfail (screenSuccess_of_not_somePairFails M h D T colors hgood))

variable [LinearOrder V] {Transcript : Type*}

/-- The actual returned low-degree rows fail with probability at most η/S.
The draft is fixed before drawing this color law; the public selector may
use the completed current-color transcript. -/
theorem returnedRowsFailure_le_budget (M : ForestModel N V) (O : FrozenOracle N V)
    (h : History N V) (draft : Position N → V) (chunkSize D T S : ℕ)
    (C s t ε ν signal η : ℝ)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ε)
    (hε : 0 ≤ ε) (hν : 0 ≤ ν) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hRT : M.TailResponseRegular C s) (hUEN : M.EdgeNondegenerate signal)
    (hfeasible : min 1 (C * t ^ s) ≤ ν) (hmargin : 4 * ε + ν < signal)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.tv (y.exactRow M.target M.target_positive j) (O.row y j) ≤ ε)
    (selector : PublicRowSelector (ResidualVertex h) Transcript)
    (transcript : (Fin T → Position N → Color) → Transcript)
    (hN : 0 < N) (hS : 0 < S) (hη : 0 < η)
    (hcolors : 8 * (D + 1) ≤ Fintype.card Color)
    (hT : 8 * Real.log ((S : ℝ) * (N : ℝ)^2 / η) ≤ (T : ℝ)) :
    (FinDist.piProduct fun _ : Fin T ↦
      FinDist.uniformColors (α := Position N) (Color := Color)).eventMass
      (fun colors ↦ ∃ j : ResidualVertex h, (residualNeighbors M h j).card ≤ D ∧
        returnedRow O h (Banks.ofOracle O t ε hfloor) draft colors chunkSize D ε
          selector (transcript colors) j ≠ residualNeighbors M h j) ≤ η / S := by
  apply (FinDist.eventMass_mono _ _ (fun colors ↦ ¬ ScreenSuccess M h colors D) ?_).trans
    (screenFailure_le_budget M h D T S η hN hS hη hcolors hT)
  rintro colors ⟨j, hdegree, hne⟩ hsuccess
  exact hne (returnedRow_eq_neighbors M O h draft colors chunkSize D C s t ε ν signal
    hfloor hε hν ht0 ht1 hRT hUEN hfeasible hmargin hrows hsuccess selector
    (transcript colors) j hdegree)

end
end Screening
end ForestSampling
