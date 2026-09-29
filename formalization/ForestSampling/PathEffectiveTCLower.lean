import ForestSampling.PathAdjacentInformation
import ForestSampling.PairInformationSymmetry
import ForestSampling.PathGeometricSums
import ForestSampling.FiniteMaskPatterns
import ForestSampling.MaskedInformationContinuity
import ForestSampling.PathEffectiveTCUpper

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling.PathClass.Parameters
noncomputable section
variable {B : ℕ}

/-- Each orientation of every strictly interior path edge retains the
same positive dependence when both endpoints and both outside neighbors
survive the four independent masking coins. -/
theorem maskedPair_information_interiorAdjacent_ge (P : Parameters B) {n : ℕ}
    {i j : Position (n + 1)} (hij : i ≠ j) (hinterior : PathGeometricSums.InteriorAdjacent i j)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    P.adjacentInformationConstant * q^4 ≤
      (MaskedInformation.maskedPairLaw (P.target (n + 1)) hij q hq0.le hq1.le).conditionalMutualInformation
        (MaskedInformation.maskedPairLaw_positive _ (P.target_positive _) hij q hq0 hq1) := by
  classical
  rcases hinterior with ⟨hd, hi0, hiN, hj0, hjN⟩
  let l : Position (n + 1) := ⟨min i.val j.val - 1, by have hh := i.isLt; omega⟩
  let r : Position (n + 1) := ⟨max i.val j.val + 1, by omega⟩
  have horder : (l.val + 1 = i.val ∧ i.val + 1 = j.val ∧ j.val + 1 = r.val) ∨
      (l.val + 1 = j.val ∧ j.val + 1 = i.val ∧ i.val + 1 = r.val) := by
    dsimp only [l, r]
    unfold Nat.dist at hd
    omega
  have hli : l ≠ i := by intro hh; have he := congrArg Fin.val hh; rcases horder with h | h <;> omega
  have hlj : l ≠ j := by intro hh; have he := congrArg Fin.val hh; rcases horder with h | h <;> omega
  have hri : r ≠ i := by intro hh; have he := congrArg Fin.val hh; rcases horder with h | h <;> omega
  have hrj : r ≠ j := by intro hh; have he := congrArg Fin.val hh; rcases horder with h | h <;> omega
  have hlr : l ≠ r := by intro hh; have he := congrArg Fin.val hh; rcases horder with h | h <;> omega
  let ls : {k : Position (n + 1) // k ≠ i ∧ k ≠ j} := ⟨l, hli, hlj⟩
  let rs : {k : Position (n + 1) // k ≠ i ∧ k ≠ j} := ⟨r, hri, hrj⟩
  let S : Finset {k : Position (n + 1) // k ≠ i ∧ k ≠ j} := {ls, rs}
  have hS : S.card = 2 := Finset.card_pair (fun hh ↦ hlr (congrArg Subtype.val hh))
  have hh := MaskedInformation.mask_pattern_le_maskedPair_information
    (P.target (n + 1)) (P.target_positive _) hij q hq0 hq1 S P.adjacentInformationConstant
    (fun y hvis ↦ by
      have hlvis := hvis ls (Finset.mem_insert_self _ _)
      have hrvis := hvis rs (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      obtain ⟨left, hleft⟩ : ∃ a, y ls = some a := by
        cases hv : y ls with
        | none => simp [hv] at hlvis
        | some a => exact ⟨a, rfl⟩
      obtain ⟨right, hright⟩ : ∃ a, y rs = some a := by
        cases hv : y rs with
        | none => simp [hv] at hrvis
        | some a => exact ⟨a, rfl⟩
      let z := MaskedInformation.outsideState i j y
      have hzi : z i = none := by simp [z, MaskedInformation.outsideState, CompleteBoundary.extension]
      have hzj : z j = none := by simp [z, MaskedInformation.outsideState, CompleteBoundary.extension, hij.symm]
      have hzl : z l = some left := by
        simpa [z, MaskedInformation.outsideState, CompleteBoundary.extension, hli, hlj, ls] using hleft
      have hzr : z r = some right := by
        simpa [z, MaskedInformation.outsideState, CompleteBoundary.extension, hri, hrj, rs] using hright
      rcases horder with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact P.exactPair_adjacent_mutualInformation_ge z l i j r h1 h2 h3 hzi hzj left right hzl hzr
      · rw [z.exactPair_mutualInformation_swap _ (P.target_positive _) j i]
        exact P.exactPair_adjacent_mutualInformation_ge z l j i r h1 h2 h3 hzj hzi left right hzl hzr)
  rw [hS] at hh
  convert hh using 1; ring

/-- The actual ordered masked-information sum retains both orientations
of all N−3 interior edges; all other terms are nonnegative. -/
theorem maskedPairInformation_ge_adjacent (P : Parameters B) (n : ℕ)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    2 * ((n + 1 - 3 : ℕ) : ℝ) * P.adjacentInformationConstant * q^4 ≤
      MaskedInformation.maskedPairInformation (P.target (n + 1)) (P.target_positive _) q hq0 hq1 := by
  have hs : (∑ i : Position (n + 1), ∑ j : Position (n + 1),
      if PathGeometricSums.InteriorAdjacent i j then P.adjacentInformationConstant * q^4 else 0) =
        2 * ((n + 1 - 3 : ℕ) : ℝ) * P.adjacentInformationConstant * q^4 := by
    have hh := PathGeometricSums.interiorAdjacent_indicator_sum (n + 1)
    calc
      _ = (∑ i : Position (n + 1), ∑ j : Position (n + 1),
          if PathGeometricSums.InteriorAdjacent i j then (1 : ℝ) else 0) *
            (P.adjacentInformationConstant * q^4) := by
        simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
      _ = _ := by rw [hh]; ring
  rw [← hs]
  unfold MaskedInformation.maskedPairInformation
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i ≠ j
  · rw [dif_pos hij]
    by_cases hint : PathGeometricSums.InteriorAdjacent i j
    · rw [if_pos hint]
      exact P.maskedPair_information_interiorAdjacent_ge hij hint q hq0 hq1
    · rw [if_neg hint]
      exact FinDist.conditionalMutualInformation_nonneg _ _
  · have heq := not_ne_iff.mp hij
    subst j
    simp [PathGeometricSums.InteriorAdjacent]

/-- The lower envelope holds for the actual positive-time masking curve. -/
theorem informationCurve_ge_adjacent (P : Parameters B) (n : ℕ) (t : ℝ) (ht : 0 < t) :
    (2 * ((n + 1 - 3 : ℕ) : ℝ) * P.adjacentInformationConstant) * Real.exp (-4*t) ≤
      MaskedInformation.informationCurve (P.target (n + 1)) (P.target_positive _) t := by
  rw [MaskedInformation.informationCurve_eq _ _ t ht]
  have he : Real.exp (-t) ^ 4 = Real.exp (-4*t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simpa only [he] using P.maskedPairInformation_ge_adjacent n (Real.exp (-t))
    (Real.exp_pos _) (by rw [Real.exp_lt_one_iff]; linarith)

/-- The effective-TC lower bound integrates the actual masked-law curve,
using only its proved continuity, nonnegativity, and exponential bounds. -/
theorem effectiveTC_ge_adjacent (P : Parameters B) (n : ℕ) :
    (2 * ((n + 1 - 3 : ℕ) : ℝ) * P.adjacentInformationConstant) * Real.exp (-4) / 4 ≤
      MaskedInformation.effectiveTC (P.target (n + 1)) (P.target_positive _) := by
  apply EffectiveTCIntegral.effectiveTCOf_ge
    (A := 2 * (n + 1 : ℝ) * Real.log 2)
  · positivity
  · exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) P.adjacentInformationConstant_pos.le
  · exact MaskedInformation.informationCurve_aestronglyMeasurable _ _
  · intro t _
    exact MaskedInformation.informationCurve_nonneg _ _ t
  · exact P.informationCurve_le n
  · exact P.informationCurve_ge_adjacent n

end
end ForestSampling.PathClass.Parameters
