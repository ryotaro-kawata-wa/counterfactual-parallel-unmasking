import ForestSampling.PathClass
import ForestSampling.FiniteMarkovInformation

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace PathClass
namespace Parameters

variable {B : ℕ}

noncomputable section

/-- The binary adjacent-type information is a scalar depending only on
the type-mass parameter, with no path-length or vocabulary-size factor. -/
def typeInformation (P : Parameters B) : ℝ :=
  ∑ s : Bool, ∑ t : Bool, P.typeJointMass s t * Real.log (P.interaction s t)

theorem kernel_kl_eq_type_sum (P : Parameters B) (x : Token B) :
    FinDist.klDivergence (P.kernel x) P.marginal =
      ∑ t : Bool, P.typeMass t *
        (P.interaction (tokenType x) t * Real.log (P.interaction (tokenType x) t)) := by
  unfold FinDist.klDivergence
  simp only [kernel_apply]
  have hcancel (y : Token B) :
      P.marginal y * P.interaction (tokenType x) (tokenType y) / P.marginal y =
        P.interaction (tokenType x) (tokenType y) :=
    mul_div_cancel_left₀ _ (P.marginal_positive y).ne'
  simp only [hcancel, mul_assoc]
  exact P.marginal_type_sum (fun t ↦
    P.interaction (tokenType x) t * Real.log (P.interaction (tokenType x) t))

/-- Emission probabilities cancel exactly in KL; this proves that the
full-vocabulary edge information equals the two-type information. -/
theorem mean_kernel_kl_eq_typeInformation (P : Parameters B) :
    (∑ x, P.marginal x * FinDist.klDivergence (P.kernel x) P.marginal) =
      P.typeInformation := by
  simp_rw [kernel_kl_eq_type_sum]
  rw [P.marginal_type_sum (fun s ↦ ∑ t : Bool,
    P.typeMass t * (P.interaction s t * Real.log (P.interaction s t)))]
  unfold typeInformation
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  unfold interaction
  field_simp [(P.typeMass_pos s).ne', (P.typeMass_pos t).ne']

/-- A visible dependence remains even in the first-token event; its
strict gap follows from `0<p<1/2`. -/
theorem kernel_first_ne_marginal (P : Parameters B) : P.kernel none ≠ P.marginal := by
  intro h
  have heq := congrArg (fun d : FinDist (Token B) ↦ d none) h
  simp only [kernel_apply, marginal_apply, tokenMass, tokenType, interaction,
    typeMass, typeJointMass] at heq
  have hp : 0 < 1 - P.p := by linarith [P.p_lt_half]
  field_simp [hp.ne'] at heq
  have hprod : 0 < P.p * (1 - 2 * P.p) :=
    mul_pos P.p_pos (by linarith [P.p_lt_half])
  nlinarith

theorem typeInformation_pos (P : Parameters B) : 0 < P.typeInformation := by
  rw [← mean_kernel_kl_eq_typeInformation]
  apply Finset.sum_pos'
  · intro x _
    exact mul_nonneg (P.marginal.nonneg x)
      (FinDist.klDivergence_nonneg _ _ (P.kernel_positive x) P.marginal_positive)
  · exact ⟨none, Finset.mem_univ _, mul_pos (P.marginal_positive none)
      (FinDist.klDivergence_pos_of_ne _ _ (P.kernel_positive none) P.marginal_positive
        P.kernel_first_ne_marginal)⟩

/-- Exact total correlation of the manuscript's actual positive path
distribution: one positive binary-type information constant per edge. -/
theorem target_totalCorrelation (P : Parameters B) (n : ℕ) :
    FinDist.totalCorrelation (P.target (n + 1)) = n * P.typeInformation := by
  rw [target, FiniteMarkovChain.totalCorrelation_law P.marginal P.kernel
    P.marginal_positive P.kernel_positive P.stationary,
    P.mean_kernel_kl_eq_typeInformation]

/-- The information constant is unchanged when only the number of
background tokens changes; its dependence on the exponent is explicit. -/
theorem typeInformation_eq_of_parameter {B' : ℕ} (P : Parameters B) (Q : Parameters B')
    (hp : P.p = Q.p) : P.typeInformation = Q.typeInformation := by
  simp only [typeInformation, interaction, typeJointMass, typeMass, hp]

end
end Parameters
end PathClass
end ForestSampling
