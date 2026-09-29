import ForestSampling.VocabularyEquivalence

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace ForestSampling

universe u v w

namespace ObservedProgram

variable {N : ℕ} {V : Type u} {W : Type v}
  [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- Change only the dependent history index along a proved equality. -/
def castHistory {h h' : History N V} (heq : h = h')
    (p : ObservedProgram N V h) : ObservedProgram N V h' := heq ▸ p

@[simp] theorem eval_castHistory (O : FrozenOracle N V) {h h' : History N V}
    (heq : h = h') (p : ObservedProgram N V h) :
    (castHistory heq p).eval O = p.eval O := by cases heq; rfl

@[simp] theorem withinOracleBudgets_castHistory (O : FrozenOracle N V) {h h' : History N V}
    (heq : h = h') (p : ObservedProgram N V h) (Q R : ℕ) :
    (castHistory heq p).WithinOracleBudgets O Q R ↔ p.WithinOracleBudgets O Q R := by
  cases heq
  rfl

/-- Relabel an actual adaptive controller. All observed probability rows
and sampled values are translated back before entering its continuation.
The batch is unchanged, and no query or commit is added. -/
def relabel (e : V ≃ W) : {h : History N V} → ObservedProgram N V h →
    ObservedProgram N W (VocabularyEquivalence.history e h)
  | _, .done complete => .done complete
  | _, .query y respects next =>
      .query (VocabularyEquivalence.state e y)
        (VocabularyEquivalence.state_respects e y _ respects)
        (fun reply ↦ relabel e (next (fun j ↦
          (reply (VocabularyEquivalence.maskedPosition e y j)).map e.symm)))
  | h, .commit batch nonempty fresh next =>
      .commit batch nonempty fresh (fun rows z ↦
        castHistory (VocabularyEquivalence.history_appendBatch_pullback e h batch fresh z)
          (relabel e (next (fun j ↦ (rows j).map e.symm) (fun j ↦ e.symm (z j)))))

/-- Every submitted-state response is translated back exactly. -/
theorem relabel_query_response (e : V ≃ W) (O : FrozenOracle N V) (y : MaskedState N V) :
    (fun j ↦ ((VocabularyEquivalence.oracle e O).readState (VocabularyEquivalence.state e y)
      (VocabularyEquivalence.maskedPosition e y j)).map e.symm) = O.readState y := by
  funext j
  rw [FrozenOracle.readState, VocabularyEquivalence.oracle_row_state, FinDist.map_equiv_symm]
  rfl

/-- Commit-row feedback is preserved, including its probability values. -/
theorem relabel_commit_response (e : V ≃ W) (O : FrozenOracle N V) (h : History N V)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted) :
    (fun j ↦ ((VocabularyEquivalence.oracle e O).commitRows
      (VocabularyEquivalence.history e h) batch fresh j).map e.symm) =
      O.commitRows h batch fresh := by
  funext j
  rw [VocabularyEquivalence.oracle_commitRows, FinDist.map_equiv_symm]

set_option maxHeartbeats 600000 in
/-- The entire output distribution, with all feedback-dependent decisions,
is transported by the public token bijection. -/
theorem eval_relabel (e : V ≃ W) (O : FrozenOracle N V) {h : History N V}
    (p : ObservedProgram N V h) :
    (p.relabel e).eval (VocabularyEquivalence.oracle e O) =
      (p.eval O).map (VocabularyEquivalence.configuration e) := by
  induction p with
  | done complete =>
      exact (FinDist.dirac_map_equiv _ (VocabularyEquivalence.configuration e)).symm
  | query y respects next ih =>
      change (relabel e (next _)).eval _ = _
      rw [relabel_query_response]
      exact ih (O.readState y)
  | @commit h batch nonempty fresh next ih =>
      change ((VocabularyEquivalence.oracle e O).commitDistribution
        (VocabularyEquivalence.history e h) batch fresh).bind _ = _
      rw [VocabularyEquivalence.oracle_commitDistribution]
      simp only [eval_castHistory, relabel_commit_response]
      ext x
      rw [FinDist.map_equiv_apply]
      change (∑ z : batch → W,
        (O.commitDistribution h batch fresh).map (Equiv.piCongrRight fun _ : batch ↦ e) z *
          (relabel e (next (O.commitRows h batch fresh) (fun j ↦ e.symm (z j)))).eval
            (VocabularyEquivalence.oracle e O) x) = _
      rw [← (Equiv.piCongrRight fun _ : batch ↦ e).sum_comp]
      apply Finset.sum_congr rfl
      intro z _
      rw [FinDist.map_equiv_apply]
      simp only [Equiv.symm_apply_apply]
      have hz : (fun j : batch ↦ e.symm ((Equiv.piCongrRight fun _ : batch ↦ e) z j)) = z := by
        funext j
        exact e.symm_apply_apply (z j)
      rw [hz, ih, FinDist.map_equiv_apply]

/-- The same Q/R limits hold after relabeling, for each actual oracle reply
and every possible realized batch assignment. -/
theorem withinOracleBudgets_relabel (e : V ≃ W) (O : FrozenOracle N V)
    {h : History N V} (p : ObservedProgram N V h) (Q R : ℕ)
    (hb : p.WithinOracleBudgets O Q R) :
    (p.relabel e).WithinOracleBudgets (VocabularyEquivalence.oracle e O) Q R := by
  induction p generalizing Q R with
  | done complete => trivial
  | query y respects next ih =>
      obtain ⟨hQ, hnext⟩ := hb
      change 0 < Q ∧ _
      refine ⟨hQ, ?_⟩
      change (relabel e (next _)).WithinOracleBudgets _ _ _
      rw [relabel_query_response]
      exact ih _ _ _ hnext
  | @commit h batch nonempty fresh next ih =>
      obtain ⟨hR, hnext⟩ := hb
      change 0 < R ∧ _
      refine ⟨hR, ?_⟩
      intro z
      rw [withinOracleBudgets_castHistory]
      rw [relabel_commit_response]
      exact ih _ _ _ _ (hnext _)

end ObservedProgram

namespace ObservedSampler

variable {N : ℕ} {V : Type u} {W : Type v} {Seed : Type w}
  [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- Relabel the public preprocessing reply before executing the translated
controller. Its seed space and random choices are unchanged. -/
def relabel (e : V ≃ W) (A : ObservedSampler N V Seed) : ObservedSampler N W Seed where
  program w reply := ObservedProgram.castHistory (VocabularyEquivalence.history_empty e)
    ((A.program w (fun j ↦ (reply ⟨j.1, by simp⟩).map e.symm)).relabel e)

/-- Exact distributional invariance includes the free preprocessing reply. -/
theorem outputLaw_relabel (e : V ≃ W) (A : ObservedSampler N V Seed) (w : Seed)
    (O : FrozenOracle N V) :
    (A.relabel e).outputLaw w (VocabularyEquivalence.oracle e O) =
      (A.outputLaw w O).map (VocabularyEquivalence.configuration e) := by
  unfold outputLaw relabel
  rw [ObservedProgram.eval_castHistory]
  have hreply : (fun j : MaskedPosition (MaskedState.allMask N V) ↦
      ((VocabularyEquivalence.oracle e O).readState (MaskedState.allMask N W)
        ⟨j.1, by simp⟩).map e.symm) = O.readState (MaskedState.allMask N V) := by
    exact ObservedProgram.relabel_query_response e O (MaskedState.allMask N V)
  rw [hreply]
  exact ObservedProgram.eval_relabel e O _

theorem withinOracleBudgets_relabel (e : V ≃ W) (A : ObservedSampler N V Seed)
    (O : FrozenOracle N V) (Q R : ℕ) (hb : A.WithinOracleBudgets O Q R) :
    (A.relabel e).WithinOracleBudgets (VocabularyEquivalence.oracle e O) Q R := by
  intro w
  change (ObservedProgram.castHistory _ _).WithinOracleBudgets _ _ _
  rw [ObservedProgram.withinOracleBudgets_castHistory]
  have hreply : (fun j : MaskedPosition (MaskedState.allMask N V) ↦
      ((VocabularyEquivalence.oracle e O).readState (MaskedState.allMask N W)
        ⟨j.1, by simp⟩).map e.symm) = O.readState (MaskedState.allMask N V) :=
    ObservedProgram.relabel_query_response e O (MaskedState.allMask N V)
  rw [hreply]
  exact ObservedProgram.withinOracleBudgets_relabel e O _ Q R (hb w)

/-- Pull a controller on the new alphabet back to an original oracle.
This form avoids requiring a syntactic round-trip identity for programs. -/
theorem outputLaw_relabel_symm (e : V ≃ W) (A : ObservedSampler N W Seed)
    (w : Seed) (O : FrozenOracle N V) :
    (A.relabel e.symm).outputLaw w O =
      (A.outputLaw w (VocabularyEquivalence.oracle e O)).map
        (VocabularyEquivalence.configuration e.symm) := by
  simpa using outputLaw_relabel e.symm A w (VocabularyEquivalence.oracle e O)

theorem withinOracleBudgets_relabel_symm (e : V ≃ W) (A : ObservedSampler N W Seed)
    (O : FrozenOracle N V) (Q R : ℕ)
    (hb : A.WithinOracleBudgets (VocabularyEquivalence.oracle e O) Q R) :
    (A.relabel e.symm).WithinOracleBudgets O Q R := by
  simpa using withinOracleBudgets_relabel e.symm A (VocabularyEquivalence.oracle e O) Q R hb

end ObservedSampler
namespace RandomizedObservedSamplerData

variable {N : ℕ} {V W : Type u}
  [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- Token relabeling keeps the arbitrary seed probability space unchanged. -/
def relabel (e : V ≃ W) (A : RandomizedObservedSamplerData N V) :
    RandomizedObservedSamplerData N W where
  Seed := A.Seed
  seedMeasurableSpace := A.seedMeasurableSpace
  seedMeasure := A.seedMeasure
  seedIsProbability := A.seedIsProbability
  sampler := A.sampler.relabel e

/-- Pointwise loss for a pulled-back controller equals its original loss
on the correspondingly transported target and oracle. -/
theorem tv_relabel_symm (e : V ≃ W) (A : RandomizedObservedSamplerData N W)
    (w : A.Seed) (I : SamplingInstance N V) (J : SamplingInstance N W)
    (htarget : J.model.target = I.model.target.map (VocabularyEquivalence.configuration e))
    (horacle : J.oracle = VocabularyEquivalence.oracle e I.oracle) :
    FinDist.tv I.model.target ((A.relabel e.symm).sampler.outputLaw w I.oracle) =
      FinDist.tv J.model.target (A.sampler.outputLaw w J.oracle) := by
  change FinDist.tv I.model.target ((A.sampler.relabel e.symm).outputLaw w I.oracle) = _
  rw [ObservedSampler.outputLaw_relabel_symm, htarget, horacle]
  have hdist := FinDist.tv_map_equiv
    (I.model.target.map (VocabularyEquivalence.configuration e))
    (A.sampler.outputLaw w (VocabularyEquivalence.oracle e I.oracle))
    (VocabularyEquivalence.configuration e).symm
  rw [FinDist.map_equiv_symm] at hdist
  exact hdist

/-- The unchanged pointwise loss gives equality of seed-averaged risks. -/
theorem risk_relabel_symm (e : V ≃ W) (A : RandomizedObservedSamplerData N W)
    (I : SamplingInstance N V) (J : SamplingInstance N W)
    (htarget : J.model.target = I.model.target.map (VocabularyEquivalence.configuration e))
    (horacle : J.oracle = VocabularyEquivalence.oracle e I.oracle) :
    (A.relabel e.symm).risk I = A.risk J := by
  unfold risk
  apply integral_congr_ae
  filter_upwards [] with w
  exact tv_relabel_symm e A w I J htarget horacle

/-- Risk measurability is transported through equality of the actual
pointwise seed loss, without adding a regularity condition on controllers. -/
theorem riskMeasurableAt_relabel_symm_iff (e : V ≃ W) (A : RandomizedObservedSamplerData N W)
    (I : SamplingInstance N V) (J : SamplingInstance N W)
    (htarget : J.model.target = I.model.target.map (VocabularyEquivalence.configuration e))
    (horacle : J.oracle = VocabularyEquivalence.oracle e I.oracle) :
    (A.relabel e.symm).RiskMeasurableAt I ↔ A.RiskMeasurableAt J := by
  letI : MeasurableSpace A.Seed := A.seedMeasurableSpace
  have hfun : (fun w : A.Seed ↦ FinDist.tv I.model.target
      ((A.relabel e.symm).sampler.outputLaw w I.oracle)) =
      (fun w : A.Seed ↦ FinDist.tv J.model.target (A.sampler.outputLaw w J.oracle)) := by
    funext w
    exact tv_relabel_symm e A w I J htarget horacle
  exact Iff.of_eq (congrArg
    (fun f : A.Seed → ℝ ↦ AEStronglyMeasurable f A.seedMeasure) hfun)

end RandomizedObservedSamplerData

end ForestSampling
