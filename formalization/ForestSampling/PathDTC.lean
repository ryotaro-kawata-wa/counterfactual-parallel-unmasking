import ForestSampling.PathInformation
import ForestSampling.MarkovDTC
import ForestSampling.MarkovConditionalInformation

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace PathClass
namespace Parameters

variable {B : ℕ}

noncomputable section

def twoStepInteraction (P : Parameters B) (s t : Bool) : ℝ :=
  ∑ u : Bool, P.typeMass u * P.interaction s u * P.interaction u t

theorem twoStepInteraction_pos (P : Parameters B) (s t : Bool) : 0 < P.twoStepInteraction s t :=
  Finset.sum_pos (fun u _ ↦ mul_pos (mul_pos (P.typeMass_pos u) (P.interaction_pos s u))
    (P.interaction_pos u t)) Finset.univ_nonempty

/-- Marginalizing the hidden middle token leaves exactly the two-type
bridge interaction; its background emission is unchanged. -/
theorem twoStep_kernel_apply (P : Parameters B) (a c : Token B) :
    FiniteMarkovChain.twoStep P.kernel a c =
      P.marginal c * P.twoStepInteraction (tokenType a) (tokenType c) := by
  unfold FiniteMarkovChain.twoStep
  rw [FinDist.bind_apply]
  simp only [kernel_apply]
  calc
    _ = P.marginal c * ∑ b, P.marginal b *
        (P.interaction (tokenType a) (tokenType b) * P.interaction (tokenType b) (tokenType c)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by
      rw [P.marginal_type_sum (fun u ↦ P.interaction (tokenType a) u *
        P.interaction u (tokenType c))]
      congr 1
      unfold twoStepInteraction
      apply Finset.sum_congr rfl
      intro u _
      ring

def typeConditionalInformation (P : Parameters B) : ℝ :=
  ∑ s : Bool, P.typeMass s * ∑ u : Bool, P.typeMass u * P.interaction s u *
    ∑ t : Bool, P.typeMass t * P.interaction u t *
      Real.log (P.interaction u t / P.twoStepInteraction s t)

theorem kernel_kl_twoStep_eq_type_sum (P : Parameters B) (a b : Token B) :
    FinDist.klDivergence (P.kernel b) (FiniteMarkovChain.twoStep P.kernel a) =
      ∑ t : Bool, P.typeMass t * (P.interaction (tokenType b) t *
        Real.log (P.interaction (tokenType b) t / P.twoStepInteraction (tokenType a) t)) := by
  unfold FinDist.klDivergence
  simp only [kernel_apply, twoStep_kernel_apply]
  have hratio (c : Token B) :
      (P.marginal c * P.interaction (tokenType b) (tokenType c)) /
        (P.marginal c * P.twoStepInteraction (tokenType a) (tokenType c)) =
      P.interaction (tokenType b) (tokenType c) / P.twoStepInteraction (tokenType a) (tokenType c) :=
    mul_div_mul_left _ _ (P.marginal_positive c).ne'
  simp only [hratio, mul_assoc]
  exact P.marginal_type_sum (fun t ↦ P.interaction (tokenType b) t *
    Real.log (P.interaction (tokenType b) t / P.twoStepInteraction (tokenType a) t))

/-- Both the retained middle token and both endpoint emissions cancel in
the actual conditional information; the resulting coefficient depends
only on the positive binary transition table. -/
theorem transitionConditionalInformation_eq_type (P : Parameters B) :
    FiniteMarkovChain.transitionConditionalInformation P.marginal P.kernel =
      P.typeConditionalInformation := by
  unfold FiniteMarkovChain.transitionConditionalInformation
  simp_rw [kernel_kl_twoStep_eq_type_sum, kernel_apply, mul_assoc]
  have hinner (a : Token B) :
      (∑ b, P.marginal b * (P.interaction (tokenType a) (tokenType b) *
        ∑ t : Bool, P.typeMass t * (P.interaction (tokenType b) t *
          Real.log (P.interaction (tokenType b) t / P.twoStepInteraction (tokenType a) t)))) =
      ∑ u : Bool, P.typeMass u * (P.interaction (tokenType a) u *
        ∑ t : Bool, P.typeMass t * (P.interaction u t *
          Real.log (P.interaction u t / P.twoStepInteraction (tokenType a) t))) :=
    P.marginal_type_sum (fun u ↦ P.interaction (tokenType a) u *
      ∑ t : Bool, P.typeMass t * (P.interaction u t *
        Real.log (P.interaction u t / P.twoStepInteraction (tokenType a) t)))
  simp only [hinner]
  rw [P.marginal_type_sum (fun s ↦ ∑ u : Bool, P.typeMass u * (P.interaction s u *
      ∑ t : Bool, P.typeMass t * (P.interaction u t *
        Real.log (P.interaction u t / P.twoStepInteraction s t))))]
  simp only [typeConditionalInformation, mul_assoc]

theorem kernel_first_ne_second (P : Parameters B) : P.kernel none ≠ P.kernel (some none) := by
  intro h
  have heq := congrArg (fun d : FinDist (Token B) ↦ d none) h
  simp only [kernel_apply, marginal_apply, tokenMass, tokenType, interaction,
    typeMass, typeJointMass] at heq
  have hp : 0 < 1 - P.p := by linarith [P.p_lt_half]
  field_simp [hp.ne', P.p_pos.ne'] at heq
  nlinarith [P.p_pos, P.p_lt_half]

theorem typeConditionalInformation_pos (P : Parameters B) : 0 < P.typeConditionalInformation := by
  rw [← P.transitionConditionalInformation_eq_type]
  exact FiniteMarkovChain.transitionConditionalInformation_pos P.marginal P.kernel
    P.marginal_positive P.kernel_positive none (some none) P.kernel_first_ne_second

/-- The exact DTC formula of the comparison proposition, established for
the actual complementary marginals of the full-vocabulary chain. -/
theorem target_dualTotalCorrelation (P : Parameters B) (n : ℕ) :
    FinDist.dualTotalCorrelation (P.target (n + 2)) =
      P.typeInformation + n * P.typeConditionalInformation := by
  rw [target, FiniteMarkovChain.dualTotalCorrelation_law P.marginal P.kernel
    P.marginal_positive P.kernel_positive P.stationary]
  rw [← FiniteMarkovChain.meanKernelKL_eq_entropy_sub P.marginal P.kernel
    P.marginal_positive P.kernel_positive P.stationary,
    P.mean_kernel_kl_eq_typeInformation,
    ← FiniteMarkovChain.transitionConditionalInformation_eq P.marginal P.kernel
      P.kernel_positive P.stationary, P.transitionConditionalInformation_eq_type]

theorem typeConditionalInformation_eq_of_parameter {B' : ℕ}
    (P : Parameters B) (Q : Parameters B') (hp : P.p = Q.p) :
    P.typeConditionalInformation = Q.typeConditionalInformation := by
  simp only [typeConditionalInformation, twoStepInteraction, interaction,
    typeJointMass, typeMass, hp]

end
end Parameters
end PathClass
end ForestSampling
