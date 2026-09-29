import ForestSampling.CollisionLedger
import ForestSampling.SurvivorQuery

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling

namespace FinDist

/-- Event probabilities in a retained dependent joint law disintegrate over
the actual first-stage outcome. -/
theorem sigmaJoint_eventMass {α : Type*} [Fintype α] {β : α → Type*}
    [∀ a, Fintype (β a)] (p : FinDist α) (k : ∀ a, FinDist (β a))
    (E : Sigma β → Prop) [DecidablePred E] :
    (sigmaJoint p k).eventMass E =
      ∑ a, p a * (k a).eventMass (fun b ↦ E ⟨a, b⟩) := by
  classical
  unfold eventMass
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : E ⟨a, b⟩ <;> simp [h, sigmaJoint_apply]

/-- A common likelihood on a finite prior event gives its exact joint mass. -/
theorem sigmaJoint_eventMass_of_constant_likelihood {α : Type*} [Fintype α]
    {β : α → Type*} [∀ a, Fintype (β a)]
    (p : FinDist α) (k : ∀ a, FinDist (β a))
    (E : Sigma β → Prop) [DecidablePred E] (F : α → Prop) [DecidablePred F]
    (c : ℝ) (hk : ∀ a, (k a).eventMass (fun b ↦ E ⟨a, b⟩) = if F a then c else 0) :
    (sigmaJoint p k).eventMass E = c * p.eventMass F := by
  rw [sigmaJoint_eventMass]
  simp_rw [hk]
  unfold eventMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : F a <;> simp [ha, mul_comm]

/-- Conditioning a retained joint law on an event of constant positive
likelihood within a prior fiber leaves exactly the prior conditioned on that
fiber. The likelihood and normalizing constant are both kept explicit. -/
theorem sigmaJoint_posterior_of_constant_likelihood {α : Type*}
    [Fintype α] [DecidableEq α] {β : α → Type*} [∀ a, Fintype (β a)]
    (p : FinDist α) (k : ∀ a, FinDist (β a))
    (E : Sigma β → Prop) [DecidablePred E] (F : α → Prop) [DecidablePred F]
    (c : ℝ) (hc : 0 < c) (hF : 0 < p.eventMass F)
    (hk : ∀ a, (k a).eventMass (fun b ↦ E ⟨a, b⟩) = if F a then c else 0) :
    (sigmaJoint p k).conditionalMap E
      (by rw [sigmaJoint_eventMass_of_constant_likelihood p k E F c hk];
          exact mul_pos hc hF) Sigma.fst = p.conditionOn F hF := by
  classical
  ext a
  rw [conditionalMap_apply_ratio,
    sigmaJoint_eventMass_of_constant_likelihood p k E F c hk]
  have hnum : (sigmaJoint p k).eventMass (fun w ↦ E w ∧ w.1 = a) =
      p a * (if F a then c else 0) := by
    rw [sigmaJoint_eventMass, Finset.sum_eq_single a]
    · simp only [and_true]
      rw [hk]
    · intro a' _ ha'
      simp [ha', eventMass]
    · simp
  rw [hnum]
  by_cases ha : F a
  · rw [if_pos ha, conditionOn_apply_of_mem _ _ _ ha]
    field_simp
  · rw [if_neg ha, conditionOn_apply_of_not_mem _ _ _ ha]
    simp

end FinDist

namespace HardMatching
open SurvivorRecord

variable {N K B : ℕ}
variable [Nonempty (HardVocabulary K B)]

/-- A finite coherent operation prefix of the actual program for a witness
instance. Its constructors use the same frozen replies, commit batches,
values, and retirement updates as `Program.retirementTrace`. -/
inductive SurvivorPrefix (P : HardLocalParameters K B) (I : InstanceIndex N K) :
    {h : History N (HardVocabulary K B)} →
    (p : Program N (HardVocabulary K B) h) →
    (r : SurvivorRecord N K) → r.Compatible I → Type 1
  | stop {h : History N (HardVocabulary K B)} (p : Program N (HardVocabulary K B) h)
      (r : SurvivorRecord N K) (hI : r.Compatible I) :
      SurvivorPrefix P I p r hI
  | query {h : History N (HardVocabulary K B)} (state : MaskedState N (HardVocabulary K B))
      (respects : state.RespectsHistory h)
      (next : (MaskedPosition state → FinDist (HardVocabulary K B)) →
        Program N (HardVocabulary K B) h)
      (r : SurvivorRecord N K) (hI : r.Compatible I)
      (tail : SurvivorPrefix P I (next ((selectedOracle P I.1 I.2).readState state))
        (r.queryUpdate I hI state) (r.compatible_queryUpdate I hI state)) :
      SurvivorPrefix P I (.query state respects next) r hI
  | commit {h : History N (HardVocabulary K B)} (batch : Finset (Position N)) (nonempty : batch.Nonempty)
      (fresh : batch ⊆ h.uncommitted)
      (next : (z : batch → HardVocabulary K B) →
        Program N (HardVocabulary K B) (h.appendBatch batch fresh z))
      (r : SurvivorRecord N K) (hI : r.Compatible I) (z : batch → HardVocabulary K B)
      (tail : SurvivorPrefix P I (next z)
        (r.commitUpdate I hI batch) (r.compatible_commitUpdate I hI batch)) :
      SurvivorPrefix P I (.commit batch nonempty fresh next) r hI

namespace SurvivorPrefix

variable {P : HardLocalParameters K B} {I : InstanceIndex N K}

noncomputable section

/-- The exact tagged observations specified by this coherent prefix. -/
def observations : {h : History N (HardVocabulary K B)} →
    {p : Program N (HardVocabulary K B) h} →
    {r : SurvivorRecord N K} → {hI : r.Compatible I} →
    SurvivorPrefix P I p r hI → List (RetirementObservation N K (HardVocabulary K B))
  | _, _, _, _, .stop _ _ _ => []
  | _, _, _, _, .query state _ _ r hI tail =>
      .query state (r.queryUpdate I hI state) :: tail.observations
  | _, _, _, _, .commit batch _ _ _ r hI z tail =>
      .commit batch z (r.commitUpdate I hI batch) :: tail.observations

/-- The survivor record at the end of this finite prefix. -/
def lastRecord : {h : History N (HardVocabulary K B)} →
    {p : Program N (HardVocabulary K B) h} →
    {r : SurvivorRecord N K} → {hI : r.Compatible I} →
    SurvivorPrefix P I p r hI → SurvivorRecord N K
  | _, _, _, _, .stop _ r _ => r
  | _, _, _, _, .query _ _ _ _ _ tail => tail.lastRecord
  | _, _, _, _, .commit _ _ _ _ _ _ _ tail => tail.lastRecord

/-- The witness's actual positive commit likelihood along the prefix. Query
steps carry no probability factor because the frozen reply is deterministic. -/
def likelihood : {h : History N (HardVocabulary K B)} →
    {p : Program N (HardVocabulary K B) h} →
    {r : SurvivorRecord N K} → {hI : r.Compatible I} →
    SurvivorPrefix P I p r hI → ℝ
  | _, _, _, _, .stop _ _ _ => 1
  | _, _, _, _, .query _ _ _ _ _ tail => tail.likelihood
  | h, _, _, _, .commit batch _ fresh _ _ _ z tail =>
      (instanceMidpointKernel P I).law h batch fresh z * tail.likelihood

theorem likelihood_pos {h : History N (HardVocabulary K B)}
    {p : Program N (HardVocabulary K B) h} {r : SurvivorRecord N K} {hI : r.Compatible I}
    (pref : SurvivorPrefix P I p r hI) : 0 < pref.likelihood := by
  induction pref with
  | stop => exact zero_lt_one
  | query state respects next r hI tail ih => exact ih
  | commit batch nonempty fresh next r hI z tail ih =>
      exact mul_pos ((instanceMidpointKernel P I).positive _ batch fresh z) ih

omit [Nonempty (HardVocabulary K B)] in
/-- The witness belongs to the final record fiber at every finite prefix. -/
theorem witness_compatible {h : History N (HardVocabulary K B)}
    {p : Program N (HardVocabulary K B) h} {r : SurvivorRecord N K} {hI : r.Compatible I}
    (pref : SurvivorPrefix P I p r hI) : pref.lastRecord.Compatible I := by
  induction pref with
  | stop p r hI => exact hI
  | query state respects next r hI tail ih => exact ih
  | commit batch nonempty fresh next r hI z tail ih => exact ih

omit [Nonempty (HardVocabulary K B)] in
/-- Final compatibility implies compatibility at every preceding boundary. -/
theorem compatible_initial_of_final {h : History N (HardVocabulary K B)}
    {p : Program N (HardVocabulary K B) h} {r : SurvivorRecord N K} {hI : r.Compatible I}
    (pref : SurvivorPrefix P I p r hI) (J : InstanceIndex N K)
    (hJ : pref.lastRecord.Compatible J) : r.Compatible J := by
  induction pref with
  | stop => exact hJ
  | query state respects next r hI tail ih =>
      exact r.compatible_queryUpdate_mono I hI state J (ih hJ)
  | commit batch nonempty fresh next r hI z tail ih =>
      exact r.compatible_commitUpdate_mono I hI batch J (ih hJ)

/-- The event that a complete actual retained trace starts with this prefix. -/
def event {h : History N (HardVocabulary K B)}
    {p : Program N (HardVocabulary K B) h} {r : SurvivorRecord N K} {hI : r.Compatible I}
    (pref : SurvivorPrefix P I p r hI) (J : InstanceIndex N K) (hJ : r.Compatible J)
    (path : Program.RetainedPath (selectedOracle P J.1 J.2) p) : Prop :=
  (Program.retirementTrace J (selectedOracle P J.1 J.2) p r hJ path).take
    pref.observations.length = pref.observations

instance eventDecidablePred {h : History N (HardVocabulary K B)}
    {p : Program N (HardVocabulary K B) h} {r : SurvivorRecord N K} {hI : r.Compatible I}
    (pref : SurvivorPrefix P I p r hI) (J : InstanceIndex N K) (hJ : r.Compatible J) :
    DecidablePred (pref.event J hJ) := by
  classical
  exact fun path ↦ inferInstanceAs (Decidable
        ((Program.retirementTrace J (selectedOracle P J.1 J.2) p r hJ path).take
          pref.observations.length = pref.observations))

/-- The number of extra queries contained in the coherent prefix. -/
def queryCount : {h : History N (HardVocabulary K B)} →
    {p : Program N (HardVocabulary K B) h} →
    {r : SurvivorRecord N K} → {hI : r.Compatible I} →
    SurvivorPrefix P I p r hI → ℕ
  | _, _, _, _, .stop _ _ _ => 0
  | _, _, _, _, .query _ _ _ _ _ tail => 1 + tail.queryCount
  | _, _, _, _, .commit _ _ _ _ _ _ _ tail => tail.queryCount

omit [Nonempty (HardVocabulary K B)] in
/-- Every query deletes at most one candidate per source, and commits delete
none. This bound holds for all labels, including already retired labels. -/
theorem candidate_card_le_final_add {h : History N (HardVocabulary K B)}
    {p : Program N (HardVocabulary K B) h} {r : SurvivorRecord N K} {hI : r.Compatible I}
    (pref : SurvivorPrefix P I p r hI) (i : Position N) :
    (r.candidates i).card ≤ (pref.lastRecord.candidates i).card + pref.queryCount := by
  induction pref with
  | stop => simp [lastRecord, queryCount]
  | query state respects next r hI tail ih =>
      have hc := r.card_queryCandidates_add_one_ge state i
      change (r.queryCandidates state i).card ≤ _ at ih
      change (r.candidates i).card ≤ (tail.lastRecord.candidates i).card +
        (1 + tail.queryCount)
      omega
  | commit batch nonempty fresh next r hI z tail ih => exact ih

/-- Truncating an actual retained path produces a coherent prefix at every
finite operation count. A count beyond termination yields the full trace. -/
def ofPath : (steps : ℕ) → {h : History N (HardVocabulary K B)} →
    (p : Program N (HardVocabulary K B) h) →
    (r : SurvivorRecord N K) → (hI : r.Compatible I) →
    Program.RetainedPath (selectedOracle P I.1 I.2) p → SurvivorPrefix P I p r hI
  | 0, _, p, r, hI, _ => .stop p r hI
  | _ + 1, _, .done complete, r, hI, _ => .stop (.done complete) r hI
  | n + 1, _, .query state respects next, r, hI, path =>
      .query state respects next r hI
        (ofPath n (next ((selectedOracle P I.1 I.2).readState state))
          (r.queryUpdate I hI state) (r.compatible_queryUpdate I hI state) path)
  | n + 1, _, .commit batch nonempty fresh next, r, hI, path =>
      .commit batch nonempty fresh next r hI path.1
        (ofPath n (next path.1) (r.commitUpdate I hI batch)
          (r.compatible_commitUpdate I hI batch) path.2)

/-- Coherent prefix observations agree exactly with the corresponding prefix
of the previously defined actual retirement trace. -/
theorem observations_ofPath (steps : ℕ) {h : History N (HardVocabulary K B)}
    (p : Program N (HardVocabulary K B) h) (r : SurvivorRecord N K) (hI : r.Compatible I)
    (path : Program.RetainedPath (selectedOracle P I.1 I.2) p) :
    (ofPath steps p r hI path).observations =
      (Program.retirementTrace I (selectedOracle P I.1 I.2) p r hI path).take steps := by
  induction steps generalizing h r with
  | zero => simp [ofPath, observations]
  | succ steps ih =>
      cases p with
      | done complete => simp [ofPath, observations, Program.retirementTrace]
      | query state respects next =>
          simp only [ofPath, observations, Program.retirementTrace, List.take_succ_cons]
          exact congrArg (List.cons _) (ih (next ((selectedOracle P I.1 I.2).readState state)) _ _ path)
      | commit batch nonempty fresh next =>
          simp only [ofPath, observations, Program.retirementTrace, List.take_succ_cons]
          exact congrArg (List.cons _) (ih _ _ _ path.2)

/-- A truncated execution cannot contain more queries than that execution. -/
theorem queryCount_ofPath_le (steps : ℕ) {h : History N (HardVocabulary K B)}
    (p : Program N (HardVocabulary K B) h) (r : SurvivorRecord N K) (hI : r.Compatible I)
    (path : Program.RetainedPath (selectedOracle P I.1 I.2) p) :
    (ofPath steps p r hI path).queryCount ≤
      Program.retainedQueryCount (selectedOracle P I.1 I.2) p path := by
  induction steps generalizing h r with
  | zero => simp [ofPath, queryCount]
  | succ steps ih =>
      cases p with
      | done complete => simp [ofPath, queryCount, Program.retainedQueryCount]
      | query state respects next =>
          exact Nat.add_le_add_left (ih (next ((selectedOracle P I.1 I.2).readState state)) _ _ path) 1
      | commit batch nonempty fresh next => exact ih _ _ _ path.2

/-- Every coherent actual prefix has one common positive likelihood on its
entire final compatible fiber, and zero likelihood outside that fiber. The
probability is taken under the actual retained midpoint program law. -/
theorem eventMass_eq_likelihood {h : History N (HardVocabulary K B)}
    {p : Program N (HardVocabulary K B) h} {r : SurvivorRecord N K} {hI : r.Compatible I}
    (pref : SurvivorPrefix P I p r hI) (hcommitted : h.committed ⊆ r.retired)
    (J : InstanceIndex N K) (hJ : r.Compatible J) :
    (Program.retainedLaw (selectedOracle P J.1 J.2) (instanceMidpointKernel P J) p).eventMass
      (pref.event J hJ) =
      if pref.lastRecord.Compatible J then pref.likelihood else 0 := by
  classical
  induction pref generalizing J with
  | stop p r hI =>
      simp [event, observations, lastRecord, likelihood, hJ, FinDist.eventMass,
        FinDist.sum_mass]
  | @query h state respects next r hI tail ih =>
      let r' := r.queryUpdate I hI state
      have hsub : r.retired ⊆ r'.retired :=
        subset_retirementClosure_left I.1 r.retired (r.queryHits I state)
      by_cases hc : r'.Compatible J
      · have hrow := (r.queryUpdate_readState_eq P I hI state J hc).symm
        have hr : r.queryUpdate J hJ state = r' :=
          ((r.queryUpdate_eq_iff I J hI hJ state).mpr hc).symm
        have ht := ih (hcommitted.trans hsub) J hc
        dsimp only [r'] at hr
        unfold event at ht ⊢
        simp only [observations, lastRecord, likelihood, Program.retainedLaw,
          Program.retirementTrace, List.length_cons, List.take_succ_cons, List.cons.injEq,
          true_and, hr]
        let f (reply : MaskedPosition state → FinDist (HardVocabulary K B)) : ℝ :=
          (Program.retainedLaw (selectedOracle P J.1 J.2) (instanceMidpointKernel P J)
            (next reply)).eventMass (fun path ↦
              (Program.retirementTrace J (selectedOracle P J.1 J.2) (next reply)
                (r.queryUpdate I hI state) hc path).take tail.observations.length =
                tail.observations)
        exact (congrArg f hrow).trans ht
      · have hr : r.queryUpdate J hJ state ≠ r' :=
          fun hh ↦ hc ((r.queryUpdate_eq_iff I J hI hJ state).mp hh.symm)
        have hfinal : ¬ tail.lastRecord.Compatible J :=
          fun hh ↦ hc (tail.compatible_initial_of_final J hh)
        dsimp only [r'] at hr
        simp [event, observations, lastRecord, hfinal, Program.retirementTrace,
          List.take_succ_cons, hr, FinDist.eventMass]
  | @commit h batch nonempty fresh next r hI z tail ih =>
      let r' := r.commitUpdate I hI batch
      have hsub : r.retired ⊆ r'.retired := subset_retirementClosure_left I.1 r.retired batch
      have hb : batch ⊆ r'.retired := subset_retirementClosure_touched I.1 r.retired batch
      have hhist : (h.appendBatch batch fresh z).committed ⊆ r'.retired := by
        rw [History.appendBatch_committed]
        exact Finset.union_subset (hcommitted.trans hsub) hb
      by_cases hc : r'.Compatible J
      · have hr : r.commitUpdate J hJ batch = r' :=
          ((r.commitUpdate_eq_iff I J hI hJ batch).mpr hc).symm
        have hk : (instanceMidpointKernel P I).law h batch fresh =
            (instanceMidpointKernel P J).law h batch fresh :=
          r.commitUpdate_midpointBatchLaw_eq P I hI h hcommitted batch fresh J hc
        dsimp only [r'] at hr
        unfold event
        simp only [observations, Program.retirementTrace, List.length_cons,
          List.take_succ_cons, List.cons.injEq, RetirementObservation.commit.injEq,
          heq_eq_eq, true_and, hr]
        change (FinDist.sigmaJoint ((instanceMidpointKernel P J).law h batch fresh)
          (fun z' ↦ Program.retainedLaw (selectedOracle P J.1 J.2)
            (instanceMidpointKernel P J) (next z'))).eventMass
          (fun path ↦ (path.1 = z ∧ True) ∧
            (Program.retirementTrace J (selectedOracle P J.1 J.2) (next path.1)
              (r.commitUpdate I hI batch) hc path.2).take tail.observations.length =
              tail.observations) = _
        rw [FinDist.sigmaJoint_eventMass, Finset.sum_eq_single z]
        · simp only [eq_self, and_true, true_and]
          change (instanceMidpointKernel P J).law h batch fresh z *
            (Program.retainedLaw (selectedOracle P J.1 J.2) (instanceMidpointKernel P J)
              (next z)).eventMass (tail.event J hc) = _
          rw [ih hhist J hc, ← hk]
          by_cases hf : tail.lastRecord.Compatible J <;>
            simp [lastRecord, likelihood, hf]
        · intro z' _ hz
          simp [FinDist.eventMass, hz]
        · simp
      · have hr : r.commitUpdate J hJ batch ≠ r' :=
          fun hh ↦ hc ((r.commitUpdate_eq_iff I J hI hJ batch).mp hh.symm)
        have hfinal : ¬ tail.lastRecord.Compatible J :=
          fun hh ↦ hc (tail.compatible_initial_of_final J hh)
        dsimp only [r'] at hr
        simp [event, observations, lastRecord, hfinal, Program.retirementTrace,
          List.take_succ_cons, hr, FinDist.eventMass]

end
end SurvivorPrefix
end HardMatching
end ForestSampling
