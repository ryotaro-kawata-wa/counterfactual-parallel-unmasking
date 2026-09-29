import ForestSampling.FiniteMaskPatterns
import ForestSampling.PathInteriorMask
import ForestSampling.PathGeometricSums
import ForestSampling.MaskedInformationContinuity
import ForestSampling.EffectiveTCIntegral

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace PathGraph
noncomputable section

/-- The strict path interior as an actual subset of the observed-background
coordinate type, with both distinguished endpoints excluded by construction. -/
def interiorOutside {N : ℕ} (i j : Position N) : Finset {k : Position N // k≠i ∧ k≠j} :=
  (interior i j).subtype (fun k ↦ k≠i ∧ k≠j)

@[simp] theorem mem_interiorOutside {N : ℕ} (i j : Position N)
    (k : {k : Position N // k≠i ∧ k≠j}) :
    k∈interiorOutside i j ↔ k.val∈interior i j := Finset.mem_subtype

theorem interiorOutside_card {N : ℕ} (i j : Position N) :
    (interiorOutside i j).card = Nat.dist i.val j.val-1 := by
  rw [interiorOutside, Finset.card_subtype,
    Finset.filter_true_of_mem (fun k hk ↦ ⟨interior_ne_left hk,interior_ne_right hk⟩), interior_card]

end
end PathGraph

namespace MaskedInformation
noncomputable section
variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Effective total correlation of the actual independently masked target
law, with the manuscript's `min(1,t)` weight and ordered endpoint pairs. -/
def effectiveTC (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive) : ℝ :=
  EffectiveTCIntegral.effectiveTCOf (informationCurve p hp)

end
end MaskedInformation

namespace PathClass.Parameters
noncomputable section
variable {B : ℕ}

/-- Actual pair conditional information under independent masks decays
with the number of possible observed separators between the endpoints. -/
theorem maskedPair_information_le_geometric (P : Parameters B) {n : ℕ}
    {i j : Position (n+1)} (hij : i≠j) (q : ℝ) (hq0 : 0<q) (hq1 : q<1) :
    (MaskedInformation.maskedPairLaw (P.target (n+1)) hij q hq0.le hq1.le).conditionalMutualInformation
        (MaskedInformation.maskedPairLaw_positive _ (P.target_positive _) hij q hq0 hq1) ≤
      q^2*Real.log 2*(1-q)^(Nat.dist i.val j.val-1) := by
  rw [← PathGraph.interiorOutside_card i j]
  apply MaskedInformation.maskedPair_information_le_mask_pattern _ (P.target_positive _)
    hij q hq0 hq1 (PathGraph.interiorOutside i j) (Real.log 2)
  · intro y
    apply P.exactPair_mutualInformation_le_log_two _ hij
    · simp [MaskedInformation.outsideState, CompleteBoundary.extension]
    · simp [MaskedInformation.outsideState, CompleteBoundary.extension, hij.symm]
  · intro y hy
    push_neg at hy
    obtain ⟨k,hk,hvisible⟩ := hy
    apply P.exactPair_mutualInformation_eq_zero_of_separator _ i j k
    · simp [MaskedInformation.outsideState, CompleteBoundary.extension]
    · simp [MaskedInformation.outsideState, CompleteBoundary.extension, hij.symm]
    · simpa [MaskedInformation.outsideState, CompleteBoundary.extension, k.2.1, k.2.2] using hvisible
    · exact (PathGraph.mem_interior i j k).mp ((PathGraph.mem_interiorOutside i j k).mp hk)

/-- Summing the exact finite geometric envelopes gives a vocabulary-free
linear bound on the actual ordered masked conditional-information sum. -/
theorem maskedPairInformation_le (P : Parameters B) (n : ℕ)
    (q : ℝ) (hq0 : 0<q) (hq1 : q<1) :
    MaskedInformation.maskedPairInformation (P.target (n+1)) (P.target_positive _) q hq0 hq1 ≤
      2*(n+1 : ℝ)*q*Real.log 2 := by
  have hc : 0 ≤ q^2*Real.log 2 := mul_nonneg (sq_nonneg _) (Real.log_nonneg (by norm_num))
  calc
    _ ≤ (q^2*Real.log 2)*(∑ i : Position (n+1), ∑ j : Position (n+1),
        if i≠j then (1-q)^(Nat.dist i.val j.val-1) else 0) := by
      unfold MaskedInformation.maskedPairInformation
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i≠j
      · simp only [dif_pos hij, if_pos hij]
        exact P.maskedPair_information_le_geometric hij q hq0 hq1
      · simp [hij]
    _ ≤ (q^2*Real.log 2)*(2*(n+1 : ℕ)/q) :=
      mul_le_mul_of_nonneg_left (PathGeometricSums.ordered_geometric_sum_le (n+1) q hq0 hq1.le) hc
    _ = _ := by push_cast; field_simp [hq0.ne'] <;> ring

/-- The actual positive-time information curve has an integrable
exponential envelope independent of the vocabulary size. -/
theorem informationCurve_le (P : Parameters B) (n : ℕ) (t : ℝ) (ht : 0<t) :
    MaskedInformation.informationCurve (P.target (n+1)) (P.target_positive _) t ≤
      (2*(n+1 : ℝ)*Real.log 2)*Real.exp (-t) := by
  rw [MaskedInformation.informationCurve_eq _ _ t ht]
  convert P.maskedPairInformation_le n (Real.exp (-t)) (Real.exp_pos _)
    (by rw [Real.exp_lt_one_iff]; linarith) using 1 <;> ring

/-- The effective-TC upper bound is obtained by direct integration of the
actual masked law, rather than an assumed comparison to TC or DTC. -/
theorem effectiveTC_le (P : Parameters B) (n : ℕ) :
    MaskedInformation.effectiveTC (P.target (n+1)) (P.target_positive _) ≤
      2*(n+1 : ℝ)*Real.log 2 := by
  apply EffectiveTCIntegral.effectiveTCOf_le
  · positivity
  · exact MaskedInformation.informationCurve_aestronglyMeasurable _ _
  · intro t _
    exact MaskedInformation.informationCurve_nonneg _ _ t
  · exact P.informationCurve_le n

end
end PathClass.Parameters
end ForestSampling
