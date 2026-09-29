import ForestSampling.PathComparisonTheorem
import ForestSampling.UpperFeasibilityGrowth
import ForestSampling.KLOracle

set_option autoImplicit false
open Filter Topology

namespace ForestSampling.PathClass
noncomputable section

/-- At any fixed public accuracy, the actual benchmark signal tends to
zero. This supplies the final membership implication for the fixed-signal
comparison path without assuming an asymptotic signal estimate. -/
theorem benchmarkSignal_tendsto_zero (radius : ℝ) :
    Tendsto (fun N : ℕ ↦ benchmarkSignal N radius) atTop (𝓝 0) := by
  have hh : Tendsto (fun N : ℕ ↦ radius^2/(N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hp := hh.rpow_const_nhds_zero (by norm_num : (0 : ℝ) < 1/3)
  simpa only [benchmarkSignal, mul_zero] using hp.const_mul (1/2 : ℝ)

/-- The exact positive path witness belongs to both actual benchmark
oracle classes eventually, uniformly in every positive background size.
No vocabulary-growth bound is needed for this membership step itself. -/
theorem benchmark_path_membership_eventually (exponent radius : ℝ)
    (he : 1 < exponent) (hr : 0 < radius) (hr1 : radius ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ (B : ℕ) (hB : 0 < B),
      let P := fromExponent B exponent he hB
      (P.model n).TailResponseRegular 1 1 ∧
      (P.model n).EdgeNondegenerate (benchmarkSignal (n+1) radius) ∧
      FiniteRankFrequency (P.model n) (P.marginalRanking n) exponent 1 ∧
      (FrozenOracle.exact (P.model n)).Accurate (P.model n) radius ∧
      (FrozenOracle.exact (P.model n)).ForwardKLAccurate (P.model n) (radius^2/(n+1 : ℕ)) := by
  let P₀ := fromExponent 1 exponent he (by norm_num)
  have ht := (benchmarkSignal_tendsto_zero radius).comp (tendsto_add_atTop_nat 1)
  have hs := ht.eventually_lt_const P₀.edgeSignal_pos
  filter_upwards [hs] with n hsN
  intro B hB P
  have heq : P.edgeSignal = P₀.edgeSignal := P.edgeSignal_eq_of_parameter P₀ rfl
  refine ⟨P.model_tailResponseRegular n, ?_, fromExponent_finiteRankFrequency n B exponent he hB,
    P.model_exactOracle_accurate n radius hr.le hr1, FrozenOracle.exact_forwardKLAccurate _ (by positivity)⟩
  apply P.model_edgeNondegenerate_of_le n (benchmarkSignal (n+1) radius)
  · exact (benchmarkSignal_bounds (n+1) radius (by omega) hr hr1).1
  · rw [heq]
    exact hsN.le

end
end ForestSampling.PathClass
