import ForestSampling.PairConditionals
import ForestSampling.PathConditionals
import ForestSampling.PathPairInformation

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace CompleteBoundary

variable {N : ℕ} {V : Type*} [DecidableEq V]

theorem update_extension_source (i j : Position N) (a b a' : V)
    (z : CompleteBoundary N V i j) :
    Function.update (extension i j a b z) i a' = extension i j a' b z := by
  funext k
  by_cases hki : k = i
  · subst k; simp [extension]
  · simp [extension, hki]

theorem update_extension_readout {i j : Position N} (hij : i ≠ j) (a b b' : V)
    (z : CompleteBoundary N V i j) :
    Function.update (extension i j a b z) j b' = extension i j a b' z := by
  funext k
  by_cases hkj : k = j
  · subst k; simp [extension, hij.symm]
  · by_cases hki : k = i
    · subst k; simp [extension, hij]
    · simp [extension, hki, hkj]

end CompleteBoundary

namespace PathClass
namespace Parameters

variable {B : ℕ}

noncomputable section

/-- Changing a token within its type changes the actual target density
only by the corresponding marginal emission factor. -/
theorem target_update_sameType_cross (P : Parameters B) {n : ℕ}
    (j : Position (n + 1)) (x : Configuration (n + 1) (Token B))
    (a b : Token B) (ht : tokenType a = tokenType b) :
    P.target (n + 1) (Function.update x j a) * P.marginal b =
      P.target (n + 1) (Function.update x j b) * P.marginal a := by
  have hh := P.target_update_local_cross j x a b
  unfold localWeight at hh
  rw [ht] at hh
  apply mul_right_cancel₀ (P.localTypeWeight_pos j x (tokenType b)).ne'
  simpa only [mul_assoc] using hh

theorem target_pair_sameTypes_cross (P : Parameters B) {n : ℕ}
    {i j : Position (n + 1)} (hij : i ≠ j) (a b a' b' : Token B)
    (ha : tokenType a = tokenType a') (hb : tokenType b = tokenType b')
    (z : CompleteBoundary (n + 1) (Token B) i j) :
    P.target (n + 1) (CompleteBoundary.extension i j a b z) * (P.marginal a' * P.marginal b') =
      P.target (n + 1) (CompleteBoundary.extension i j a' b' z) * (P.marginal a * P.marginal b) := by
  have h1 := P.target_update_sameType_cross i (CompleteBoundary.extension i j a b z) a a' ha
  have h2 := P.target_update_sameType_cross j (CompleteBoundary.extension i j a' b z) b b' hb
  simp only [CompleteBoundary.update_extension_source] at h1
  simp only [CompleteBoundary.update_extension_readout hij] at h2
  calc
    _ = (P.target (n + 1) (CompleteBoundary.extension i j a b z) * P.marginal a') * P.marginal b' := by ring
    _ = (P.target (n + 1) (CompleteBoundary.extension i j a' b z) * P.marginal b') * P.marginal a := by rw [h1]; ring
    _ = _ := by rw [h2]; ring

/-- The emission cross-product identity survives summation over every
unobserved outside coordinate and actual conditional normalization. -/
theorem exactPair_sameTypes_cross (P : Parameters B) {n : ℕ}
    (y : MaskedState (n + 1) (Token B)) {i j : Position (n + 1)} (hij : i ≠ j)
    (hi : y i = none) (hj : y j = none) (a b a' b' : Token B)
    (ha : tokenType a = tokenType a') (hb : tokenType b = tokenType b') :
    y.exactPair (P.target (n + 1)) (P.target_positive _) i j (a, b) * (P.marginal a' * P.marginal b') =
      y.exactPair (P.target (n + 1)) (P.target_positive _) i j (a', b') * (P.marginal a * P.marginal b) := by
  classical
  have hratio (a b : Token B) :
      y.exactPair (P.target (n + 1)) (P.target_positive _) i j (a, b) =
        (P.target (n + 1)).eventMass (fun x ↦ y.Agrees x ∧ (x i, x j) = (a, b)) /
          (P.target (n + 1)).eventMass y.Agrees :=
    FinDist.conditionalMap_apply_ratio _ y.Agrees (y.probability_pos _ (P.target_positive _))
      (fun x ↦ (x i, x j)) (a, b)
  rw [hratio, hratio]
  rw [MaskedState.eventMass_agrees_pair _ y hij, MaskedState.eventMass_agrees_pair _ y hij]
  simp only [div_mul_eq_mul_div]
  congr 1
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : y.Agrees (CompleteBoundary.extension i j a b z)
  · have hz' := (y.agrees_pair_extension_iff hi hj a b a' b' z).mp hz
    simp only [hz, hz', ite_true]
    exact P.target_pair_sameTypes_cross hij a b a' b' ha hb z
  · have hz' : ¬ y.Agrees (CompleteBoundary.extension i j a' b' z) :=
      fun hh ↦ hz ((y.agrees_pair_extension_iff hi hj a b a' b' z).mpr hh)
    simp [hz, hz']

def typeRepresentative : Bool → Token B
  | false => none
  | true => some none

@[simp] theorem tokenType_representative (s : Bool) :
    tokenType (typeRepresentative (B := B) s) = s := by cases s <;> rfl

/-- The positive type-pair factor of the actual partially conditioned
pair law, obtained from its representative-token probabilities. -/
def pairTypeFactor (P : Parameters B) {n : ℕ} (y : MaskedState (n + 1) (Token B))
    (i j : Position (n + 1)) (s t : Bool) : ℝ :=
  y.exactPair (P.target (n + 1)) (P.target_positive _) i j
    (typeRepresentative s, typeRepresentative t) /
      (P.marginal (typeRepresentative s) * P.marginal (typeRepresentative t))

theorem pairTypeFactor_pos (P : Parameters B) {n : ℕ}
    (y : MaskedState (n + 1) (Token B)) {i j : Position (n + 1)} (hij : i ≠ j)
    (hi : y i = none) (hj : y j = none) (s t : Bool) :
    0 < P.pairTypeFactor y i j s t :=
  div_pos (y.exactPair_positive _ (P.target_positive _) hij hi hj _)
    (mul_pos (P.marginal_positive _) (P.marginal_positive _))

/-- Every actual conditional pair has independent within-type emissions,
for arbitrary outside observations and masks. No posterior factorization
is assumed in deriving this equality. -/
theorem exactPair_emission_form (P : Parameters B) {n : ℕ}
    (y : MaskedState (n + 1) (Token B)) {i j : Position (n + 1)} (hij : i ≠ j)
    (hi : y i = none) (hj : y j = none) (a b : Token B) :
    y.exactPair (P.target (n + 1)) (P.target_positive _) i j (a, b) =
      P.marginal a * P.marginal b * P.pairTypeFactor y i j (tokenType a) (tokenType b) := by
  have hh := P.exactPair_sameTypes_cross y hij hi hj a b
    (typeRepresentative (tokenType a)) (typeRepresentative (tokenType b)) (by simp) (by simp)
  unfold pairTypeFactor
  rw [← mul_div_assoc]
  apply (eq_div_iff (mul_ne_zero (P.marginal_positive _).ne' (P.marginal_positive _).ne')).mpr
  simpa only [mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using hh

/-- The actual two-token posterior carries at most one bit of mutual
information, uniformly in vocabulary size and all outside histories. -/
theorem exactPair_mutualInformation_le_log_two (P : Parameters B) {n : ℕ}
    (y : MaskedState (n + 1) (Token B)) {i j : Position (n + 1)} (hij : i ≠ j)
    (hi : y i = none) (hj : y j = none) :
    (y.exactPair (P.target (n + 1)) (P.target_positive _) i j).mutualInformation ≤ Real.log 2 :=
  P.pair_mutualInformation_le_log_two _ (P.pairTypeFactor y i j)
    (P.pairTypeFactor_pos y hij hi hj) (P.exactPair_emission_form y hij hi hj)

end
end Parameters
end PathClass
end ForestSampling
