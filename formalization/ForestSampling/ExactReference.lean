import ForestSampling.AdaptiveHellinger

set_option autoImplicit false

open scoped BigOperators

namespace ForestSampling

/-!
# Exact joint-reference execution

The analysis-only reference retains every frozen query reply but replaces a
commit by the target's joint conditional law on the selected batch. Unlike the
product of exact singleton rows, this reference is valid for unsafe batches.
-/

namespace FinDist

variable {α β : Type*} [Fintype α] [Fintype β]

/-- A conditional readout mass is the mass of the corresponding joint event,
divided by the conditioning-event mass. -/
theorem conditionalMap_apply_ratio (p : FinDist α) (E : α → Prop)
    [DecidablePred E] (hE : 0 < p.eventMass E) (f : α → β)
    [DecidableEq β] (b : β) :
    p.conditionalMap E hE f b =
      p.eventMass (fun a ↦ E a ∧ f a = b) / p.eventMass E := by
  classical
  unfold conditionalMap
  rw [map_apply]
  unfold eventMass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hEa : E a <;> by_cases hfa : f a = b <;>
    simp [conditionOn, hEa, hfa, eventMass]

/-- Finite disintegration over a readout partition. The kernel at each
readout value is the original law conditioned on that value and the initial
event. Each fiber is assumed to have positive mass. -/
theorem conditionalMap_bind_conditionOn (p : FinDist α) (E : α → Prop)
    [DecidablePred E] (hE : 0 < p.eventMass E) (f : α → β)
    [DecidableEq β]
    (hf : ∀ b, 0 < p.eventMass (fun a ↦ E a ∧ f a = b)) :
    (p.conditionalMap E hE f).bind
      (fun b ↦ p.conditionOn (fun a ↦ E a ∧ f a = b) (hf b)) =
      p.conditionOn E hE := by
  classical
  ext a
  rw [bind_apply]
  by_cases hEa : E a
  · rw [Finset.sum_eq_single (f a)]
    · rw [conditionalMap_apply_ratio, conditionOn_apply_of_mem _ _ _ ⟨hEa, rfl⟩,
        conditionOn_apply_of_mem _ _ _ hEa]
      field_simp [ne_of_gt (hf (f a))]
    · intro b _ hba
      have hab : f a ≠ b := Ne.symm hba
      simp [conditionOn, hab]
    · simp
  · simp [conditionOn, hEa]

/-- Equivalent conditioning events give the same conditional law. -/
theorem conditionOn_congr (p : FinDist α) (E F : α → Prop)
    [DecidablePred E] [DecidablePred F]
    (hE : 0 < p.eventMass E) (hF : 0 < p.eventMass F)
    (h : ∀ a, E a ↔ F a) : p.conditionOn E hE = p.conditionOn F hF := by
  have hm := p.eventMass_congr E F h
  ext a
  by_cases ha : E a
  · simp [conditionOn, ha, (h a).mp ha, hm]
  · have hFa : ¬ F a := fun hFa ↦ ha ((h a).mpr hFa)
    simp [conditionOn, ha, hFa]

end FinDist

namespace History

variable {N : ℕ} {V : Type*} [DecidableEq V]

/-- Agreement after a fresh batch commit is precisely agreement with the old
history together with the selected batch values. -/
theorem agrees_appendBatch_iff (h : History N V)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted)
    (z : batch → V) (x : Configuration N V) :
    (h.appendBatch batch fresh z).Agrees x ↔
      h.Agrees x ∧ (fun i : batch ↦ x i.1) = z := by
  constructor
  · intro hx
    constructor
    · intro i
      have hxi := hx ⟨i.1, Finset.mem_union_left batch i.2⟩
      simpa only [appendBatch_value_old] using hxi
    · funext i
      have hxi := hx ⟨i.1, Finset.mem_union_right h.committed i.2⟩
      simpa only [appendBatch_value_new] using hxi
  · rintro ⟨hold, hbatch⟩ i
    by_cases hi : i.1 ∈ h.committed
    · simpa [appendBatch, hi] using hold ⟨i.1, hi⟩
    · have hiBatch : i.1 ∈ batch :=
        (Finset.mem_union.mp i.2).resolve_left hi
      have hxi := congrFun hbatch ⟨i.1, hiBatch⟩
      simpa [appendBatch, hi] using hxi

variable [Fintype V] [Nonempty V]

/-- The true joint conditional for the whole selected batch, rather than the
product of its singleton conditional distributions. -/
noncomputable def jointBatchLaw (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) (h : History N V)
    (batch : Finset (Position N)) : FinDist (batch → V) :=
  p.conditionalMap h.Agrees (h.probability_pos p hp)
    (fun x i ↦ x i.1)

/-- Every assignment to a fresh batch has positive probability under the
joint conditional, since it can be extended to a full assignment. -/
theorem jointBatchLaw_strictlyPositive
    (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    (h : History N V) (batch : Finset (Position N))
    (fresh : batch ⊆ h.uncommitted) :
    (h.jointBatchLaw p hp batch).StrictlyPositive := by
  unfold jointBatchLaw
  refine p.conditionalMap_strictlyPositive hp h.Agrees
    (h.probability_pos p hp) (fun (x : Configuration N V) (i : batch) ↦ x i.1) ?_
  intro z
  obtain ⟨x, hx⟩ := (h.appendBatch batch fresh z).agrees_nonempty
  exact ⟨x, (h.agrees_appendBatch_iff batch fresh z x).mp hx⟩

/-- Each singleton marginal of the joint batch conditional is the history's
exact singleton row. This identifies the marginals used in total correlation. -/
theorem jointBatchLaw_map_eval
    (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    (h : History N V) (batch : Finset (Position N)) (j : batch) :
    (h.jointBatchLaw p hp batch).map (fun z ↦ z j) = h.exactRow p hp j.1 := by
  simp only [jointBatchLaw, exactRow, FinDist.conditionalMap,
    FinDist.map_comp, Function.comp_def]

/-- Disintegrating the target conditional over any fresh batch and then
conditioning on its realized values recovers the original conditional law. -/
theorem jointBatchLaw_bind_conditionalLaw
    (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    (h : History N V) (batch : Finset (Position N))
    (fresh : batch ⊆ h.uncommitted) :
    (h.jointBatchLaw p hp batch).bind
      (fun z ↦ (h.appendBatch batch fresh z).conditionalLaw p hp) =
      h.conditionalLaw p hp := by
  classical
  let f : Configuration N V → (batch → V) := fun x i ↦ x i.1
  have hevent (z : batch → V) (x : Configuration N V) :
      h.Agrees x ∧ f x = z ↔ (h.appendBatch batch fresh z).Agrees x :=
    (h.agrees_appendBatch_iff batch fresh z x).symm
  have hf (z : batch → V) :
      0 < p.eventMass (fun x ↦ h.Agrees x ∧ f x = z) := by
    rw [p.eventMass_congr _ _ (hevent z)]
    exact (h.appendBatch batch fresh z).probability_pos p hp
  have hkernel (z : batch → V) :
      p.conditionOn (fun x ↦ h.Agrees x ∧ f x = z) (hf z) =
        (h.appendBatch batch fresh z).conditionalLaw p hp := by
    exact p.conditionOn_congr _ _ _ _ (hevent z)
  have hdisintegration := p.conditionalMap_bind_conditionOn h.Agrees
    (h.probability_pos p hp) f hf
  simpa only [hkernel, jointBatchLaw, conditionalLaw, f] using hdisintegration

/-- Conditioning on the empty committed history leaves the target unchanged. -/
@[simp]
theorem conditionalLaw_empty (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) :
    (History.empty N V).conditionalLaw p hp = p := by
  have hevery (x : Configuration N V) : (History.empty N V).Agrees x := by
    intro i
    exact False.elim (Finset.notMem_empty i.1 i.2)
  have hmass : p.eventMass (History.empty N V).Agrees = 1 := by
    calc
      p.eventMass (History.empty N V).Agrees = p.eventMass (fun _ ↦ True) :=
        p.eventMass_congr _ _ (fun x ↦ iff_true_intro (hevery x))
      _ = 1 := p.eventMass_true
  ext x
  simp [conditionalLaw, FinDist.conditionOn, hevery x, hmass]

/-- A completed history leaves a point mass at its recorded full assignment. -/
theorem conditionalLaw_of_complete (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) (h : History N V)
    (complete : h.committed = Finset.univ) :
    h.conditionalLaw p hp = FinDist.dirac (h.completedConfiguration complete) := by
  have hevent (x : Configuration N V) :
      h.Agrees x ↔ x = h.completedConfiguration complete := by
    constructor
    · intro hx
      funext i
      exact hx ⟨i, by rw [complete]; simp⟩
    · intro hx
      subst x
      intro i
      rfl
  have hmass : p.eventMass h.Agrees = p (h.completedConfiguration complete) := by
    unfold FinDist.eventMass
    simp_rw [hevent]
    exact Fintype.sum_ite_eq' _ _
  ext x
  by_cases hx : x = h.completedConfiguration complete
  · subst x
    simp [conditionalLaw, FinDist.conditionOn, hevent, hmass,
      FinDist.dirac_apply, ne_of_gt (hp (h.completedConfiguration complete))]
  · simp [conditionalLaw, FinDist.conditionOn, hevent, hx, FinDist.dirac_apply]

end History

namespace MaskedState

variable {N : ℕ} {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- The mandatory commit state contains exactly the committed-history event. -/
theorem commitState_agrees_iff (h : History N V) (x : Configuration N V) :
    (commitState h).Agrees x ↔ h.Agrees x := by
  constructor
  · intro hx i
    apply hx i.1 (h.value i)
    simp [commitState, i.2]
  · intro hx i a hia
    by_cases hi : i ∈ h.committed
    · have hvalue : h.value ⟨i, hi⟩ = a := by
        simpa [commitState, hi] using hia
      exact (hx ⟨i, hi⟩).trans hvalue
    · simp [commitState, hi] at hia

variable [Fintype V] [Nonempty V]

/-- The exact commit-state row is the corresponding singleton conditional
of the committed history, with the same conditioning event. -/
theorem exactRow_commitState (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) (h : History N V)
    (j : MaskedPosition (commitState h)) :
    (commitState h).exactRow p hp j = h.exactRow p hp j.1 := by
  apply p.conditionalMap_congr _ _ _ _ _ _
  · exact commitState_agrees_iff h
  · intro x
    rfl

end MaskedState

namespace Program

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Evaluate the analysis-only joint-reference process. Frozen queries and
the adaptive controller are retained; only each batch's sampling law is
replaced by the target's exact joint conditional at its committed history. -/
noncomputable def evalJointReference (target : FinDist (Configuration N V))
    (hpositive : target.StrictlyPositive) (queryOracle : FrozenOracle N V) :
    {h : History N V} → Program N V h → FinDist (Configuration N V)
  | h, .done complete => FinDist.dirac (h.completedConfiguration complete)
  | _h, .query state _respects next =>
      evalJointReference target hpositive queryOracle
        (next (queryOracle.readState state))
  | h, .commit batch _nonempty _fresh next =>
      (h.jointBatchLaw target hpositive batch).bind fun z ↦
        evalJointReference target hpositive queryOracle (next z)

/-- The adaptive joint reference returns the target conditional law from
every committed history. This holds for arbitrary complete programs and
requires no structural safety or oracle accuracy. -/
theorem evalJointReference_eq_conditionalLaw
    (target : FinDist (Configuration N V)) (hpositive : target.StrictlyPositive)
    (queryOracle : FrozenOracle N V)
    {h : History N V} (p : Program N V h) :
    evalJointReference target hpositive queryOracle p =
      h.conditionalLaw target hpositive := by
  induction p with
  | @done h complete =>
      exact (h.conditionalLaw_of_complete target hpositive complete).symm
  | query state respects next ih =>
      exact ih (queryOracle.readState state)
  | @commit h batch nonempty fresh next ih =>
      simp only [evalJointReference]
      calc
        (h.jointBatchLaw target hpositive batch).bind
            (fun z ↦ evalJointReference target hpositive queryOracle (next z)) =
            (h.jointBatchLaw target hpositive batch).bind
              (fun z ↦ (h.appendBatch batch fresh z).conditionalLaw target hpositive) := by
          congr 1
          funext z
          exact ih z
        _ = h.conditionalLaw target hpositive :=
          h.jointBatchLaw_bind_conditionalLaw target hpositive batch fresh

end Program

namespace Sampler

variable {N : ℕ} {V Seed : Type*}
variable [Fintype V] [DecidableEq V] [Nonempty V]

/-- Fixed-seed output of the true-joint reference, retaining the original
oracle's distinguished preprocessing reply and all subsequent query replies. -/
noncomputable def jointReferenceOutputLaw (A : Sampler N V Seed)
    (M : ForestModel N V) (w : Seed) (O : FrozenOracle N V) :
    FinDist (Configuration N V) :=
  Program.evalJointReference M.target M.target_positive O
    (A.program w (O.readState (MaskedState.allMask N V)))

/-- The true-joint reference output is exactly the target for every fixed
seed, regardless of the batches selected by the adaptive controller. -/
theorem jointReferenceOutputLaw_eq_target (A : Sampler N V Seed)
    (M : ForestModel N V) (w : Seed) (O : FrozenOracle N V) :
    A.jointReferenceOutputLaw M w O = M.target := by
  unfold jointReferenceOutputLaw
  rw [Program.evalJointReference_eq_conditionalLaw, History.conditionalLaw_empty]

end Sampler

end ForestSampling
