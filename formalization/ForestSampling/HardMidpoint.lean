import ForestSampling.CurrentStatements
import ForestSampling.MatchingCombinatorics
import ForestSampling.ProgramMidpoint
import ForestSampling.Minimax

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace NonlinearMatchingParameters

variable {N : ℕ}

noncomputable section

/-- The positive background block supplies an actual vocabulary token. -/
theorem vocabularyNonempty (P : NonlinearMatchingParameters N) :
    Nonempty (HardVocabulary P.bankSize P.backgroundSize) :=
  ⟨Sum.inr ⟨0, P.backgroundSize_pos⟩⟩

/-- The even-length matching and nonempty bank make the hard family nonempty. -/
theorem instanceIndex_nonempty (P : NonlinearMatchingParameters N) :
    Nonempty (HardMatching.InstanceIndex N P.bankSize) :=
  HardMatching.instanceIndex_nonempty P.even_length P.bank_nonempty

/-- The initial hard-instance prior, independent of the algorithm's seed. -/
def instancePrior (P : NonlinearMatchingParameters N) :
    FinDist (HardMatching.InstanceIndex N P.bankSize) :=
  HardMatching.uniformInstancePrior P.even_length P.bank_nonempty

/-- A complete analytic outcome retains both the hidden instance and the
actual adaptive program path selected under that instance's frozen oracle. -/
abbrev MidpointOutcome (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) :=
  (I : HardMatching.InstanceIndex N P.bankSize) ×
    Program.RetainedPath (P.hardFamily I).oracle
      (A.program w ((P.hardFamily I).oracle.readState
        (MaskedState.allMask N (HardVocabulary P.bankSize P.backgroundSize))))

instance midpointOutcomeFintype (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) : Fintype (P.MidpointOutcome A w) :=
  inferInstanceAs (Fintype (Sigma _))

/-- The genuine instance--midpoint joint law used by the lower proof.
The instance is sampled from the fixed prior; every commit then uses the
normalized geometric mean of joint target and product-oracle batch laws. -/
def midpointJoint (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) : FinDist (P.MidpointOutcome A w) := by
  letI := P.vocabularyNonempty
  exact FinDist.sigmaJoint P.instancePrior
    (fun I ↦ A.midpointPathLaw (P.hardFamily I).model w (P.hardFamily I).oracle)

/-- The accumulated affinity penalty of an actual analytic outcome. -/
def midpointPenalty (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) (outcome : P.MidpointOutcome A w) : ℝ := by
  letI := P.vocabularyNonempty
  exact 1 - A.midpointPathWeight (P.hardFamily outcome.1).model w
    (P.hardFamily outcome.1).oracle outcome.2

/-- Average Hellinger loss is exactly the expected penalty under the
instance--midpoint law, for the real sampler and the fixed seed. -/
theorem prior_sqHellinger_eq_midpoint_penalty (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) :
    (∑ I, P.instancePrior I * FinDist.sqHellinger (P.hardFamily I).model.target
      (A.outputLaw w (P.hardFamily I).oracle)) =
    ∑ outcome, P.midpointJoint A w outcome * P.midpointPenalty A w outcome := by
  let := P.vocabularyNonempty
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro I _
  rw [A.output_sqHellinger_eq_midpoint_loss]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro path _
  change _ = (P.instancePrior I *
    A.midpointPathLaw (P.hardFamily I).model w (P.hardFamily I).oracle path) * _
  unfold midpointPenalty
  ring

/-- Convert to TV before integrating over arbitrary seeds, so no additional
Hellinger measurability is required beyond the stored admissibility condition. -/
theorem midpoint_penalty_le_prior_tv (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) :
    (∑ outcome, P.midpointJoint A w outcome * P.midpointPenalty A w outcome) ≤
    ∑ I, P.instancePrior I * FinDist.tv (P.hardFamily I).model.target
      (A.outputLaw w (P.hardFamily I).oracle) := by
  rw [← P.prior_sqHellinger_eq_midpoint_penalty]
  apply Finset.sum_le_sum
  intro I _
  exact mul_le_mul_of_nonneg_left (FinDist.sqHellinger_le_tv _ _)
    (P.instancePrior.nonneg I)

/-- The remaining probabilistic lower-bound obligation can be expressed
entirely on the actual joint instance--midpoint process. This is a conditional
bridge, not a proof that the process has the required collision penalty. -/
theorem le_minimax_of_midpoint_penalty (P : NonlinearMatchingParameters N)
    (Q R : ℕ) (hR : 1 ≤ R) (c : ℝ)
    (hpenalty : ∀ A : InstanceFamily.BudgetedSampler P.hardFamily Q R,
      ∀ w : A.1.Seed,
      c ≤ ∑ outcome, P.midpointJoint A.1.sampler w outcome *
        P.midpointPenalty A.1.sampler w outcome) :
    c ≤ InstanceFamily.minimax P.hardFamily Q R := by
  apply InstanceFamily.le_minimax_of_seedwise_prior_of_one_le_rounds
    P.hardFamily P.instancePrior Q R hR c
  intro A w
  exact (hpenalty A w).trans (P.midpoint_penalty_le_prior_tv A.1.sampler w)

end
end NonlinearMatchingParameters
end ForestSampling
