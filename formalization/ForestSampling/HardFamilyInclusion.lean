import ForestSampling.HardEdgeDistance
import ForestSampling.CurrentStatements
import ForestSampling.ScreeningProbes

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace HardMatching

variable {N K B : ℕ} [Nonempty (HardVocabulary K B)]

/-- On a matched source/readout pair, a complete boundary leaves the exact
row equal to the already normalized local endpoint kernel. -/
theorem boundaryRow_eq_endpointKernel (P : HardLocalParameters K B)
    (M : PerfectMatching N) (trigger : Position N → Fin K)
    {i j : Position N} (hij : i ≠ j) (hmate : M.mate j = i)
    (z : CompleteBoundary N (HardVocabulary K B) i j) (a : HardVocabulary K B) :
    (model P M trigger).target.boundaryRow (model P M trigger).target_positive i j a z =
      P.endpointKernel (trigger i) (trigger j) a := by
  rw [← MaskedState.exactRow_boundaryState (model P M trigger) hij a z,
    exactRowCharacterization P M trigger]
  simp [idealRow, MaskedState.boundaryState, hmate, hij]

/-- If source and readout are not matched, the fixed complete boundary
already determines the readout's mate. Varying the source cannot change its row. -/
theorem boundaryRow_eq_of_not_matched (P : HardLocalParameters K B)
    (M : PerfectMatching N) (trigger : Position N → Fin K)
    {i j : Position N} (hij : i ≠ j) (hmate : M.mate j ≠ i)
    (z : CompleteBoundary N (HardVocabulary K B) i j) (a b : HardVocabulary K B) :
    (model P M trigger).target.boundaryRow (model P M trigger).target_positive i j a z =
      (model P M trigger).target.boundaryRow (model P M trigger).target_positive i j b z := by
  rw [← MaskedState.exactRow_boundaryState (model P M trigger) hij a z,
    ← MaskedState.exactRow_boundaryState (model P M trigger) hij b z,
    exactRowCharacterization P M trigger, exactRowCharacterization P M trigger]
  simp [idealRow, MaskedState.boundaryState, hmate, M.mate_ne_self j]

/-- Every oriented matching edge has intrinsic response exactly the coupling
parameter, uniformly over all complete boundary assignments. -/
theorem directedResponse_eq_coupling (P : HardLocalParameters K B)
    (M : PerfectMatching N) (trigger : Position N → Fin K)
    {i j : Position N} (hedge : (model P M trigger).graph.Adj i j)
    (z : CompleteBoundary N (HardVocabulary K B) i j) :
    (model P M trigger).directedResponse hedge.ne z = P.edgeCoupling := by
  have hmate : M.mate j = i := hedge.symm
  apply le_antisymm
  · apply Finset.sup'_le
    intro ab _
    rw [boundaryRow_eq_endpointKernel P M trigger hedge.ne hmate,
      boundaryRow_eq_endpointKernel P M trigger hedge.ne hmate]
    exact P.endpointKernel_tv_le_coupling (trigger i) (trigger j) ab.1 ab.2
  · obtain ⟨a, b, hab⟩ := P.endpointKernel_tv_coupling_attained (trigger i) (trigger j)
    have h := (model P M trigger).pair_response_le_directedResponse hedge.ne z a b
    rw [boundaryRow_eq_endpointKernel P M trigger hedge.ne hmate,
      boundaryRow_eq_endpointKernel P M trigger hedge.ne hmate, hab] at h
    exact h

/-- The hard target satisfies the actual two-sided uniform edge-signal
assumption whenever the public positive signal is below its coupling. -/
theorem model_edgeNondegenerate (P : HardLocalParameters K B)
    (M : PerfectMatching N) (trigger : Position N → Fin K)
    (signal : ℝ) (hsignal : 0 < signal) (hle : signal ≤ P.edgeCoupling) :
    (model P M trigger).EdgeNondegenerate signal := by
  refine ⟨hsignal, by linarith [P.coupling_le_trigger, P.trigger_le_half], ?_⟩
  intro i j hedge z
  rw [directedResponse_eq_coupling P M trigger hedge z]
  exact hle

/-- The hard target satisfies response-tail regularity with exponent and
constant one. A tail below the candidate mass cannot contain the trigger,
and every other response is bounded by coupling≤trigger mass. -/
theorem model_tailResponseRegular (P : HardLocalParameters K B)
    (M : PerfectMatching N) (trigger : Position N → Fin K) :
    (model P M trigger).TailResponseRegular 1 1 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro i j hij t ht0 _ht1 z a b ha hb
  simp only [Real.rpow_one, one_mul]
  by_cases hmate : M.mate j = i
  · rw [boundaryRow_eq_endpointKernel P M trigger hij hmate,
      boundaryRow_eq_endpointKernel P M trigger hij hmate]
    by_cases ht : P.triggerMass ≤ t
    · exact (P.endpointKernel_tv_le_coupling (trigger i) (trigger j) a b).trans
        (P.coupling_le_trigger.trans ht)
    · have ha' : a ≠ Sum.inl (trigger i) := by
        intro heq
        rw [ForestModel.mem_tailSet_iff, model_marginal, heq] at ha
        exact ht ha
      have hb' : b ≠ Sum.inl (trigger i) := by
        intro heq
        rw [ForestModel.mem_tailSet_iff, model_marginal, heq] at hb
        exact ht hb
      rw [P.endpointKernel_tv_eq_feature_difference,
        P.feature_off_trigger (trigger i) ha', P.feature_off_trigger (trigger i) hb']
      simpa using ht0
  · rw [boundaryRow_eq_of_not_matched P M trigger hij hmate z a b, FinDist.tv_self]
    exact ht0

/-- The concrete selected oracle belongs to the A2 class under exactly the
finite cubic-scale inclusion inequality and the declared public radius domain. -/
theorem model_oracleAccurate (P : HardLocalParameters K B)
    (M : PerfectMatching N) (trigger : Position N → Fin K)
    (radius : ℝ) (hr0 : 0 ≤ radius) (hr1 : radius ≤ 1)
    (hscale : P.edgeCoupling ^ 2 * P.triggerMass ≤ radius ^ 2 / (2 * (N : ℝ))) :
    (selectedOracle P M trigger).Accurate (model P M trigger) radius :=
  selectedOracle_accurate P M trigger radius hr0 hr1 hscale

end HardMatching
end ForestSampling
