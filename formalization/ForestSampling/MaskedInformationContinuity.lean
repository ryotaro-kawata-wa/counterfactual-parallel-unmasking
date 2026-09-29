import ForestSampling.FiniteMaskedInformation
import ForestSampling.FiniteInformationContinuity

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory

namespace ForestSampling

namespace FinDist

variable {T ι α : Type*} [TopologicalSpace T] [Fintype ι] [DecidableEq ι]
  [Fintype α] [DecidableEq α]

/-- Every mask-pattern weight is a finite product of continuous linear
factors in the visible-coordinate probability. -/
theorem continuous_maskWeight (y : ι → Option α) (q : T → ℝ) (hq : Continuous q) :
    Continuous (fun t ↦ maskWeight y (q t)) := by
  unfold maskWeight
  apply continuous_finsetProd
  intro i _
  by_cases hy : (y i).isSome
  · simp only [hy]
    exact hq
  · simp only [hy]
    exact continuous_const.sub hq

/-- The actual masked atom mass factors into its polynomial mask weight
and a fixed event probability under the original target. -/
theorem continuous_maskedLaw_mass (p : FinDist (ι → α)) (q : T → ℝ)
    (hq : Continuous q) (hq0 : ∀ t, 0 ≤ q t) (hq1 : ∀ t, q t ≤ 1)
    (y : ι → Option α) :
    Continuous (fun t ↦ p.maskedLaw (q t) (hq0 t) (hq1 t) y) := by
  simp only [maskedLaw_apply]
  exact (continuous_maskWeight y q hq).mul continuous_const

end FinDist

namespace MaskedInformation

noncomputable section

variable {N : ℕ} {V T : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [TopologicalSpace T]

/-- Reindexing the actual masked observation to background and endpoint
coordinates preserves continuous atom masses. -/
theorem continuous_maskedPairLaw_mass (p : FinDist (Configuration N V))
    {i j : Position N} (hij : i ≠ j) (q : T → ℝ) (hq : Continuous q)
    (hq0 : ∀ t, 0 ≤ q t) (hq1 : ∀ t, q t ≤ 1)
    (yab : CompleteBoundary N (Option V) i j × (Option V × Option V)) :
    Continuous (fun t ↦ maskedPairLaw p hij (q t) (hq0 t) (hq1 t) yab) := by
  simp only [maskedPairLaw, FinDist.map_equiv_apply]
  exact FinDist.continuous_maskedLaw_mass p q hq hq0 hq1 _

/-- Actual conditional information of a masked endpoint pair is continuous
where the visible-coordinate probability is strictly between zero and one. -/
theorem continuous_maskedPair_conditionalMutualInformation
    (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    {i j : Position N} (hij : i ≠ j) (q : T → ℝ) (hq : Continuous q)
    (hq0 : ∀ t, 0 < q t) (hq1 : ∀ t, q t < 1) :
    Continuous (fun t ↦ (maskedPairLaw p hij (q t) (hq0 t).le (hq1 t).le).conditionalMutualInformation (maskedPairLaw_positive p hp hij (q t) (hq0 t) (hq1 t))) := by
  apply FinDist.continuous_conditionalMutualInformation
  intro yab
  exact continuous_maskedPairLaw_mass p hij q hq (fun t ↦ (hq0 t).le) (fun t ↦ (hq1 t).le) yab

/-- The ordered-pair conditional-information sum of the actual
independently masked target distribution. -/
def maskedPairInformation (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) : ℝ :=
  ∑ i : Position N, ∑ j : Position N, if hij : i ≠ j then
    (maskedPairLaw p hij q hq0.le hq1.le).conditionalMutualInformation
      (maskedPairLaw_positive p hp hij q hq0 hq1) else 0

/-- The full finite ordered sum is continuous on the same probability
domain, with no assumed regularity of its conditional information. -/
theorem continuous_maskedPairInformation (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) (q : T → ℝ) (hq : Continuous q)
    (hq0 : ∀ t, 0 < q t) (hq1 : ∀ t, q t < 1) :
    Continuous (fun t ↦ maskedPairInformation p hp (q t) (hq0 t) (hq1 t)) := by
  unfold maskedPairInformation
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  by_cases hij : i ≠ j
  · simp only [dif_pos hij]
    exact continuous_maskedPair_conditionalMutualInformation p hp hij q hq hq0 hq1
  · simp only [dif_neg hij]
    exact continuous_const

theorem maskedPairInformation_nonneg (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    0 ≤ maskedPairInformation p hp q hq0 hq1 := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact FinDist.conditionalMutualInformation_nonneg _ _
  · exact le_rfl

/-- The comparison integrand at q = exp(-t). Its arbitrary extension by
zero for nonpositive times has no effect on integration over Ioi 0. -/
def informationCurve (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive) (t : ℝ) : ℝ :=
  if ht : 0 < t then maskedPairInformation p hp (Real.exp (-t)) (Real.exp_pos _)
    (by rw [Real.exp_lt_one_iff]; linarith) else 0

/-- On positive times this is precisely the actual masked-information sum. -/
theorem informationCurve_eq (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    (t : ℝ) (ht : 0 < t) :
    informationCurve p hp t = maskedPairInformation p hp (Real.exp (-t)) (Real.exp_pos _)
      (by rw [Real.exp_lt_one_iff]; linarith) := by
  simp only [informationCurve, dif_pos ht]

/-- The information curve is continuous on the positive-time subtype. -/
theorem informationCurve_continuous_restrict (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) :
    Continuous (fun t : Set.Ioi (0 : ℝ) ↦ informationCurve p hp t.1) := by
  have hq : Continuous (fun t : Set.Ioi (0 : ℝ) ↦ Real.exp (-t.1)) :=
    Real.continuous_exp.comp continuous_subtype_val.neg
  have hq0 : ∀ t : Set.Ioi (0 : ℝ), 0 < Real.exp (-t.1) := fun t ↦ Real.exp_pos _
  have hq1 : ∀ t : Set.Ioi (0 : ℝ), Real.exp (-t.1) < 1 := by
    intro t
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos t.2
  have hc := continuous_maskedPairInformation p hp _ hq hq0 hq1
  apply hc.congr
  intro t
  exact (informationCurve_eq p hp t.1 t.2).symm

/-- Actual continuity on the integral's open domain. -/
theorem informationCurve_continuousOn (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) : ContinuousOn (informationCurve p hp) (Set.Ioi 0) :=
  continuousOn_iff_continuous_domRestrict.mpr (informationCurve_continuous_restrict p hp)

/-- The measurability needed by the Bochner integral follows from actual
finite-law continuity; it is not an extra comparison-theorem assumption. -/
theorem informationCurve_aestronglyMeasurable (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) :
    AEStronglyMeasurable (informationCurve p hp) (volume.restrict (Set.Ioi 0)) :=
  (informationCurve_continuousOn p hp).aestronglyMeasurable measurableSet_Ioi

theorem informationCurve_nonneg (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) (t : ℝ) : 0 ≤ informationCurve p hp t := by
  unfold informationCurve
  split_ifs
  · exact maskedPairInformation_nonneg _ _ _ _ _
  · exact le_rfl

end
end MaskedInformation
end ForestSampling
