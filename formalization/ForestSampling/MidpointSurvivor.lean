import ForestSampling.SurvivorPosterior
import ForestSampling.HardMidpoint

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace NonlinearMatchingParameters
open HardMatching HardMatching.SurvivorRecord

variable {N : ℕ}

noncomputable section

/-- A coherent finite prefix of the actual sampler at a fixed seed and a
witness hard instance, starting from the empty analytic record. -/
abbrev MidpointPrefix (P : NonlinearMatchingParameters N) {Seed : Type*}
    (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed) (w : Seed)
    (I : InstanceIndex N P.bankSize) :=
  SurvivorPrefix P.toHardLocal I
    (A.program w ((P.hardFamily I).oracle.readState
      (MaskedState.allMask N (HardVocabulary P.bankSize P.backgroundSize))))
    (initial N P.bankSize) (compatible_initial I)

/-- The actual instance--midpoint event specified by a coherent prefix.
It retains the observed retired edges, exposed triggers, and commit values. -/
def midpointPrefixEvent (P : NonlinearMatchingParameters N) {Seed : Type*}
    {A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed} {w : Seed}
    {I : InstanceIndex N P.bankSize} (pref : P.MidpointPrefix A w I)
    (outcome : P.MidpointOutcome A w) : Prop :=
  (Program.retirementTrace outcome.1 (P.hardFamily outcome.1).oracle
    (A.program w ((P.hardFamily outcome.1).oracle.readState
      (MaskedState.allMask N (HardVocabulary P.bankSize P.backgroundSize))))
    (initial N P.bankSize) (compatible_initial outcome.1) outcome.2).take
      pref.observations.length = pref.observations

instance midpointPrefixEventDecidablePred (P : NonlinearMatchingParameters N) {Seed : Type*}
    {A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed} {w : Seed}
    {I : InstanceIndex N P.bankSize} (pref : P.MidpointPrefix A w I) :
    DecidablePred (P.midpointPrefixEvent pref) := by
  classical
  exact fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- The actual sampler prefix has a common positive likelihood on its exact
final record fiber. The initial free all-mask reply is proved common, so it
cannot select different root programs across hidden instances. -/
theorem midpointPrefix_likelihood (P : NonlinearMatchingParameters N) {Seed : Type*}
    {A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed} {w : Seed}
    {I : InstanceIndex N P.bankSize} (pref : P.MidpointPrefix A w I)
    (J : InstanceIndex N P.bankSize) :
    let := P.vocabularyNonempty
    (A.midpointPathLaw (P.hardFamily J).model w (P.hardFamily J).oracle).eventMass
      (fun path ↦ P.midpointPrefixEvent pref ⟨J, path⟩) =
      if pref.lastRecord.Compatible J then pref.likelihood else 0 := by
  classical
  let := P.vocabularyNonempty
  have ht := pref.eventMass_eq_likelihood (by simp [History.empty_committed])
    J (compatible_initial J)
  unfold SurvivorPrefix.event at ht
  unfold midpointPrefixEvent
  let f (reply : MaskedPosition
      (MaskedState.allMask N (HardVocabulary P.bankSize P.backgroundSize)) →
      FinDist (HardVocabulary P.bankSize P.backgroundSize)) : ℝ :=
    (Program.retainedLaw (selectedOracle P.toHardLocal J.1 J.2)
      (instanceMidpointKernel P.toHardLocal J) (A.program w reply)).eventMass
      (fun path ↦
        (Program.retirementTrace J (selectedOracle P.toHardLocal J.1 J.2)
          (A.program w reply) (initial N P.bankSize) (compatible_initial J) path).take
            pref.observations.length = pref.observations)
  have hr : (selectedOracle P.toHardLocal J.1 J.2).readState
      (MaskedState.allMask N (HardVocabulary P.bankSize P.backgroundSize)) =
      (selectedOracle P.toHardLocal I.1 I.2).readState
        (MaskedState.allMask N (HardVocabulary P.bankSize P.backgroundSize)) :=
    (readState_allMask_common P.toHardLocal J.1 J.2).trans
      (readState_allMask_common P.toHardLocal I.1 I.2).symm
  exact (congrArg f hr).trans ht

/-- The final compatible fiber is nonempty because it contains the witness. -/
theorem midpointPrefix_fiber_nonempty (P : NonlinearMatchingParameters N) {Seed : Type*}
    {A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed} {w : Seed}
    {I : InstanceIndex N P.bankSize} (pref : P.MidpointPrefix A w I) :
    Nonempty {J : InstanceIndex N P.bankSize // pref.lastRecord.Compatible J} :=
  ⟨⟨I, pref.witness_compatible⟩⟩

/-- Every coherent prefix has positive probability under the actual
instance--midpoint joint law. -/
theorem midpointPrefix_eventMass_pos (P : NonlinearMatchingParameters N) {Seed : Type*}
    {A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed} {w : Seed}
    {I : InstanceIndex N P.bankSize} (pref : P.MidpointPrefix A w I) :
    0 < (P.midpointJoint A w).eventMass (P.midpointPrefixEvent pref) := by
  classical
  let := P.vocabularyNonempty
  let := P.instanceIndex_nonempty
  let := P.midpointPrefix_fiber_nonempty pref
  have hf : 0 < P.instancePrior.eventMass pref.lastRecord.Compatible :=
    FinDist.uniform_eventMass_pos _
  change 0 < (FinDist.sigmaJoint P.instancePrior
    (fun J ↦ A.midpointPathLaw (P.hardFamily J).model w (P.hardFamily J).oracle)).eventMass _
  rw [FinDist.sigmaJoint_eventMass_of_constant_likelihood _ _ _
    pref.lastRecord.Compatible pref.likelihood (P.midpointPrefix_likelihood pref)]
  exact mul_pos pref.likelihood_pos hf

/-- The actual adaptive survivor invariant: after every coherent observed
prefix, the hidden instance is exactly uniform over its final compatible
fiber. This is derived from actual program likelihoods, including the
normalized geometric midpoint kernels and the free initial oracle reply. -/
theorem midpointPrefix_posterior (P : NonlinearMatchingParameters N) {Seed : Type*}
    {A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed} {w : Seed}
    {I : InstanceIndex N P.bankSize} (pref : P.MidpointPrefix A w I) :
    let := P.midpointPrefix_fiber_nonempty pref
    (P.midpointJoint A w).conditionalMap (P.midpointPrefixEvent pref)
      (P.midpointPrefix_eventMass_pos pref) Sigma.fst = pref.lastRecord.uniformExtensions := by
  classical
  let := P.vocabularyNonempty
  let := P.instanceIndex_nonempty
  let := P.midpointPrefix_fiber_nonempty pref
  have hf : 0 < P.instancePrior.eventMass pref.lastRecord.Compatible :=
    FinDist.uniform_eventMass_pos _
  calc
    _ = P.instancePrior.conditionOn pref.lastRecord.Compatible hf :=
      FinDist.sigmaJoint_posterior_of_constant_likelihood P.instancePrior
        (fun J ↦ A.midpointPathLaw (P.hardFamily J).model w (P.hardFamily J).oracle)
        (P.midpointPrefixEvent pref) pref.lastRecord.Compatible pref.likelihood
        pref.likelihood_pos hf (P.midpointPrefix_likelihood pref)
    _ = _ := pref.lastRecord.prior_conditionOn_compatible P.even_length P.bank_nonempty hf

/-- Every actual complete outcome supplies a coherent prefix at any finite
operation count, including counts after the program has terminated. -/
def midpointPrefixOfPath (P : NonlinearMatchingParameters N) {Seed : Type*}
    (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed) (w : Seed)
    (outcome : P.MidpointOutcome A w) (steps : ℕ) : P.MidpointPrefix A w outcome.1 :=
  SurvivorPrefix.ofPath steps _ _ _ outcome.2

/-- Exact coverage: no actual retained trace prefix is excluded by the
coherent-prefix representation used in the posterior theorem. -/
theorem midpointPrefixOfPath_observations (P : NonlinearMatchingParameters N) {Seed : Type*}
    (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed) (w : Seed)
    (outcome : P.MidpointOutcome A w) (steps : ℕ) :
    (P.midpointPrefixOfPath A w outcome steps).observations =
      (Program.retirementTrace outcome.1 (P.hardFamily outcome.1).oracle
        (A.program w ((P.hardFamily outcome.1).oracle.readState
          (MaskedState.allMask N (HardVocabulary P.bankSize P.backgroundSize))))
        (initial N P.bankSize) (compatible_initial outcome.1) outcome.2).take steps := by
  let := P.vocabularyNonempty
  exact SurvivorPrefix.observations_ofPath steps _ _ _ outcome.2

/-- After a coherent prefix with q queries, each remaining candidate set has
at least K−q labels. Commits have no effect on this counting argument. -/
theorem midpointPrefix_candidate_card (P : NonlinearMatchingParameters N) {Seed : Type*}
    {A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed} {w : Seed}
    {I : InstanceIndex N P.bankSize} (pref : P.MidpointPrefix A w I) (i : Position N) :
    P.bankSize - pref.queryCount ≤ (pref.lastRecord.candidates i).card := by
  have hc := pref.candidate_card_le_final_add i
  simpa only [initial, Finset.card_univ, Fintype.card_fin] using Nat.sub_le_iff_le_add.mpr hc

/-- The query-disclosure hazard under the actual conditioned midpoint joint
law: an unretired source can hit its displayed trigger with probability at
most 1/(K−q), where q is the exact number of preceding extra queries. -/
theorem midpointPrefix_hit_probability_le (P : NonlinearMatchingParameters N) {Seed : Type*}
    {A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed} {w : Seed}
    {I : InstanceIndex N P.bankSize} (pref : P.MidpointPrefix A w I)
    (state : MaskedState N (HardVocabulary P.bankSize P.backgroundSize))
    (i : pref.lastRecord.Survivor) (hq : pref.queryCount < P.bankSize) :
    ((P.midpointJoint A w).conditionalMap (P.midpointPrefixEvent pref)
      (P.midpointPrefix_eventMass_pos pref) Sigma.fst).eventMass
      (fun J ↦ state i.1 = some (Sum.inl (J.2 i.1))) ≤
      ((P.bankSize - pref.queryCount : ℕ) : ℝ)⁻¹ := by
  classical
  let := P.midpointPrefix_fiber_nonempty pref
  rw [P.midpointPrefix_posterior]
  unfold uniformExtensions
  rw [FinDist.map_eventMass]
  exact pref.lastRecord.uniform_fiber_hit_probability_le_remaining state i pref.queryCount hq
    (P.midpointPrefix_candidate_card pref i.1)

end
end NonlinearMatchingParameters
end ForestSampling
