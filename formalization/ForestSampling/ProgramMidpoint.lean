import ForestSampling.Algorithm
import ForestSampling.AdaptiveMidpoint
import ForestSampling.ExactReference

set_option autoImplicit false

open scoped BigOperators

namespace ForestSampling

universe u v w

/-!
# Retained executions and replay for the sampler program

Oracle queries follow the fixed oracle in every execution.  The retained
path records each sampled batch, and the no-remasking interface makes the
terminal configuration sufficient to reconstruct that path.
-/

namespace History

variable {N : ℕ} {V : Type u}

/-- Reading a completed history preserves all values that history records. -/
theorem completedConfiguration_agrees (h : History N V)
    (complete : h.committed = Finset.univ) :
    h.Agrees (h.completedConfiguration complete) := by
  intro i
  rfl

/-- A completed history has only one compatible complete configuration. -/
theorem completedConfiguration_eq_of_agrees (h : History N V)
    (complete : h.committed = Finset.univ) (x : Configuration N V)
    (hx : h.Agrees x) : h.completedConfiguration complete = x := by
  funext i
  exact (hx ⟨i, by rw [complete]; simp⟩).symm

end History

namespace FinDist

noncomputable section

/-- Marginalizing a retained two-stage law agrees with the corresponding
mixture of the stagewise output laws. -/
theorem sigmaJoint_map {α : Type u} [Fintype α]
    {β : α → Type v} [∀ a, Fintype (β a)]
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    (p : FinDist α) (k : (a : α) → FinDist (β a)) (f : Sigma β → γ) :
    (sigmaJoint p k).map f =
      p.bind (fun a ↦ (k a).map (fun b ↦ f ⟨a, b⟩)) := by
  ext y
  rw [map_apply, Fintype.sum_sigma, bind_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : f ⟨a, b⟩ = y <;> simp [h]

end

end FinDist

/-- A positive law for each permissible fresh batch at each history.
The interface changes only commit draws, leaving oracle queries untouched. -/
structure BatchKernel (N : ℕ) (V : Type u) [Fintype V] [DecidableEq V] where
  law : (h : History N V) → (batch : Finset (Position N)) →
    batch ⊆ h.uncommitted → FinDist (batch → V)
  positive : ∀ h batch fresh, (law h batch fresh).StrictlyPositive

namespace BatchKernel

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

noncomputable section

/-- The implemented sampler draws independently from the frozen oracle rows. -/
def ofOracle (O : FrozenOracle N V) : BatchKernel N V where
  law := O.commitDistribution
  positive h batch fresh := FinDist.piProduct_strictlyPositive
    (fun j ↦ O.row_positive (MaskedState.commitState h)
      (FrozenOracle.commitReadout h batch fresh j))

/-- Exact joint conditionals give the comparison execution's batch kernels. -/
def ofTarget [Nonempty V] (target : FinDist (Configuration N V))
    (hpositive : target.StrictlyPositive) : BatchKernel N V where
  law h batch _fresh := h.jointBatchLaw target hpositive batch
  positive h batch fresh :=
    h.jointBatchLaw_strictlyPositive target hpositive batch fresh

/-- The analytic midpoint changes each batch law to its normalized geometric
mean while preserving its history and selected coordinate set. -/
def midpoint (K L : BatchKernel N V) : BatchKernel N V where
  law h batch fresh := FinDist.midpoint (K.law h batch fresh)
    (L.law h batch fresh) (K.positive h batch fresh) (L.positive h batch fresh)
  positive h batch fresh := FinDist.midpoint_strictlyPositive
    (K.law h batch fresh) (L.law h batch fresh)
    (K.positive h batch fresh) (L.positive h batch fresh)

end

end BatchKernel

namespace Program

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- Complete execution paths with all sampled batch values retained.
Queries have a unique successor because their frozen oracle is fixed. -/
def RetainedPath (O : FrozenOracle N V) :
    {h : History N V} → Program N V h → Type u
  | _, .done _ => PUnit
  | _, .query state _ next => RetainedPath O (next (O.readState state))
  | _, .commit batch _ _ next => (z : batch → V) × RetainedPath O (next z)

noncomputable instance retainedPathFintype (O : FrozenOracle N V)
    {h : History N V} (p : Program N V h) : Fintype (RetainedPath O p) := by
  induction p with
  | done complete => exact inferInstanceAs (Fintype PUnit)
  | query state respects next ih => exact ih (O.readState state)
  | commit batch nonempty fresh next ih =>
      letI : ∀ z, Fintype (RetainedPath O (next z)) := ih
      exact inferInstanceAs
        (Fintype ((z : batch → V) × RetainedPath O (next z)))

/-- The complete configuration produced by one retained execution path. -/
def retainedOutput (O : FrozenOracle N V) :
    {h : History N V} → (p : Program N V h) →
      RetainedPath O p → Configuration N V
  | h, .done complete, _ => h.completedConfiguration complete
  | _, .query state _ next, path =>
      retainedOutput O (next (O.readState state)) path
  | _, .commit _ _ _ next, path => retainedOutput O (next path.1) path.2

/-- Replay a program by supplying the selected coordinates of a complete
configuration at every commit. Existing committed values remain fixed. -/
def replay (O : FrozenOracle N V) :
    {h : History N V} → (p : Program N V h) →
      Configuration N V → RetainedPath O p
  | _, .done _, _ => PUnit.unit
  | _, .query state _ next, x => replay O (next (O.readState state)) x
  | _, .commit batch _ _ next, x =>
      ⟨fun j : batch ↦ x j, replay O (next (fun j : batch ↦ x j)) x⟩

/-- No execution can alter values that were already committed. -/
theorem retainedOutput_agrees (O : FrozenOracle N V)
    {h : History N V} (p : Program N V h) (path : RetainedPath O p) :
    h.Agrees (retainedOutput O p path) := by
  induction p with
  | @done h complete => exact h.completedConfiguration_agrees complete
  | query state respects next ih => exact ih (O.readState state) path
  | @commit h batch nonempty fresh next ih =>
      have hchild := ih path.1 path.2
      intro i
      simpa only [retainedOutput, History.appendBatch_value_old] using
        hchild ⟨i.1, Finset.mem_union_left batch i.2⟩

/-- Replay gives the supplied output whenever it extends the current history. -/
theorem retainedOutput_replay (O : FrozenOracle N V)
    {h : History N V} (p : Program N V h) (x : Configuration N V)
    (hx : h.Agrees x) : retainedOutput O p (replay O p x) = x := by
  induction p with
  | @done h complete => exact h.completedConfiguration_eq_of_agrees complete x hx
  | query state respects next ih => exact ih (O.readState state) hx
  | @commit h batch nonempty fresh next ih =>
      apply ih (fun j : batch ↦ x j)
      intro i
      by_cases hi : i.1 ∈ h.committed
      · rw [show (h.appendBatch batch fresh (fun j : batch ↦ x j)).value i =
          h.value ⟨i.1, hi⟩ by exact h.appendBatch_value_old batch fresh _ ⟨i.1, hi⟩]
        exact hx ⟨i.1, hi⟩
      · have hib : i.1 ∈ batch := (Finset.mem_union.mp i.2).resolve_left hi
        exact (h.appendBatch_value_new batch fresh
          (fun j : batch ↦ x j) ⟨i.1, hib⟩).symm

/-- The first differing batch would differ in a coordinate of the final
output, so distinct retained executions cannot merge into one output. -/
theorem retainedOutput_injective (O : FrozenOracle N V)
    {h : History N V} (p : Program N V h) :
    Function.Injective (retainedOutput O p) := by
  induction p with
  | done complete =>
      intro a b _
      cases a
      cases b
      rfl
  | query state respects next ih => exact ih (O.readState state)
  | @commit h batch nonempty fresh next ih =>
      rintro ⟨z, child⟩ ⟨z', child'⟩ hout
      have hz : z = z' := by
        funext j
        have ha := retainedOutput_agrees O (next z) child
        have hb := retainedOutput_agrees O (next z') child'
        have ha' := (ha ⟨j.1, Finset.mem_union_right h.committed j.2⟩).trans
          (h.appendBatch_value_new batch fresh z j)
        have hb' := (hb ⟨j.1, Finset.mem_union_right h.committed j.2⟩).trans
          (h.appendBatch_value_new batch fresh z' j)
        exact ha'.symm.trans ((congrFun hout j.1).trans hb')
      subst z'
      exact Sigma.ext rfl (heq_of_eq (ih z hout))

/-- Every retained path is reconstructed by replaying its terminal output. -/
theorem replay_retainedOutput (O : FrozenOracle N V)
    {h : History N V} (p : Program N V h) (path : RetainedPath O p) :
    replay O p (retainedOutput O p path) = path := by
  apply retainedOutput_injective O p
  exact retainedOutput_replay O p _ (retainedOutput_agrees O p path)

/-- Replay is a proved equivalence between terminal execution paths and the
configurations compatible with the starting history. -/
def retainedEquiv (O : FrozenOracle N V) {h : History N V}
    (p : Program N V h) :
    RetainedPath O p ≃ {x : Configuration N V // h.Agrees x} where
  toFun path := ⟨retainedOutput O p path, retainedOutput_agrees O p path⟩
  invFun x := replay O p x.1
  left_inv := replay_retainedOutput O p
  right_inv x := by
    apply Subtype.ext
    exact retainedOutput_replay O p x.1 x.2

/-- Starting from the empty history, complete outputs and retained paths are
in bijection; this is a conclusion of the program interface, not a hypothesis. -/
def retainedOutputEquiv (O : FrozenOracle N V)
    (p : Program N V (History.empty N V)) :
    RetainedPath O p ≃ Configuration N V where
  toFun := retainedOutput O p
  invFun := replay O p
  left_inv := replay_retainedOutput O p
  right_inv x := by
    apply retainedOutput_replay O p x
    intro i
    exact False.elim (Finset.notMem_empty i.1 i.2)

/-- Counted counterfactual submissions on a retained execution path. -/
def retainedQueryCount (O : FrozenOracle N V) :
    {h : History N V} → (p : Program N V h) → RetainedPath O p → ℕ
  | _, .done _, _ => 0
  | _, .query state _ next, path =>
      1 + retainedQueryCount O (next (O.readState state)) path
  | _, .commit _ _ _ next, path => retainedQueryCount O (next path.1) path.2

/-- Nonempty commit rounds on a retained execution path. -/
def retainedRoundCount (O : FrozenOracle N V) :
    {h : History N V} → (p : Program N V h) → RetainedPath O p → ℕ
  | _, .done _, _ => 0
  | _, .query state _ next, path =>
      retainedRoundCount O (next (O.readState state)) path
  | _, .commit _ _ _ next, path => 1 + retainedRoundCount O (next path.1) path.2

/-- The original pathwise budget bounds hold on every retained path, hence
also under the analytic midpoint law that assigns probabilities to them. -/
theorem retainedPath_withinBudgets (O : FrozenOracle N V)
    {h : History N V} (p : Program N V h) (path : RetainedPath O p)
    (Q R : ℕ) (hbudget : WithinBudgets p Q R) :
    retainedQueryCount O p path ≤ Q ∧ retainedRoundCount O p path ≤ R := by
  induction p generalizing Q R with
  | done complete => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | query state respects next ih =>
      obtain ⟨hQ, hnext⟩ := hbudget
      obtain ⟨hq, hr⟩ := ih (O.readState state) path (Q - 1) R
        (hnext (O.readState state))
      change 1 + retainedQueryCount O (next (O.readState state)) path ≤ Q ∧
        retainedRoundCount O (next (O.readState state)) path ≤ R
      omega
  | commit batch nonempty fresh next ih =>
      obtain ⟨hR, hnext⟩ := hbudget
      obtain ⟨hq, hr⟩ := ih path.1 path.2 Q (R - 1) (hnext path.1)
      change retainedQueryCount O (next path.1) path.2 ≤ Q ∧
        1 + retainedRoundCount O (next path.1) path.2 ≤ R
      omega

noncomputable section

/-- A retained execution with fixed query replies and the specified batch law. -/
def retainedLaw (O : FrozenOracle N V) (K : BatchKernel N V) :
    {h : History N V} → (p : Program N V h) → FinDist (RetainedPath O p)
  | _, .done _ => FinDist.dirac (α := PUnit) PUnit.unit
  | _, .query state _ next => retainedLaw O K (next (O.readState state))
  | h, .commit batch _ fresh next =>
      FinDist.sigmaJoint (K.law h batch fresh) (fun z ↦ retainedLaw O K (next z))

/-- Local-affinity product along the actual program's retained execution. -/
def retainedAffinityWeight (O : FrozenOracle N V) (K L : BatchKernel N V) :
    {h : History N V} → (p : Program N V h) → RetainedPath O p → ℝ
  | _, .done _, _ => 1
  | _, .query state _ next, path =>
      retainedAffinityWeight O K L (next (O.readState state)) path
  | h, .commit batch _ fresh next, path =>
      FinDist.affinity (K.law h batch fresh) (L.law h batch fresh) *
        retainedAffinityWeight O K L (next path.1) path.2

theorem retainedAffinityWeight_nonneg (O : FrozenOracle N V)
    (K L : BatchKernel N V) {h : History N V}
    (p : Program N V h) (path : RetainedPath O p) :
    0 ≤ retainedAffinityWeight O K L p path := by
  induction p with
  | done complete => exact zero_le_one
  | query state respects next ih => exact ih (O.readState state) path
  | @commit h batch nonempty fresh next ih =>
      exact mul_nonneg (FinDist.affinity_nonneg _ _) (ih path.1 path.2)

theorem retainedAffinityWeight_le_one (O : FrozenOracle N V)
    (K L : BatchKernel N V) {h : History N V}
    (p : Program N V h) (path : RetainedPath O p) :
    retainedAffinityWeight O K L p path ≤ 1 := by
  induction p with
  | done complete => exact le_rfl
  | query state respects next ih => exact ih (O.readState state) path
  | @commit h batch nonempty fresh next ih =>
      exact mul_le_one₀ (FinDist.affinity_le_one _ _)
        (retainedAffinityWeight_nonneg O K L (next path.1) path.2) (ih path.1 path.2)

/-- The geometric-mean mass identity on paths generated by the actual program. -/
theorem retained_mass_factorization (O : FrozenOracle N V)
    (K L : BatchKernel N V) {h : History N V}
    (p : Program N V h) (path : RetainedPath O p) :
    Real.sqrt (retainedLaw O K p path * retainedLaw O L p path) =
      retainedLaw O (K.midpoint L) p path * retainedAffinityWeight O K L p path := by
  induction p with
  | done complete =>
      cases path
      simp [retainedLaw, retainedAffinityWeight]
  | query state respects next ih => exact ih (O.readState state) path
  | @commit h batch nonempty fresh next ih =>
      change Real.sqrt ((K.law h batch fresh path.1 * retainedLaw O K (next path.1) path.2) *
          (L.law h batch fresh path.1 * retainedLaw O L (next path.1) path.2)) =
        (FinDist.midpoint (K.law h batch fresh) (L.law h batch fresh)
            (K.positive h batch fresh) (L.positive h batch fresh) path.1 *
          retainedLaw O (K.midpoint L) (next path.1) path.2) *
        (FinDist.affinity (K.law h batch fresh) (L.law h batch fresh) *
          retainedAffinityWeight O K L (next path.1) path.2)
      rw [show (K.law h batch fresh path.1 * retainedLaw O K (next path.1) path.2) *
          (L.law h batch fresh path.1 * retainedLaw O L (next path.1) path.2) =
        (K.law h batch fresh path.1 * L.law h batch fresh path.1) *
          (retainedLaw O K (next path.1) path.2 * retainedLaw O L (next path.1) path.2)
        by ring]
      rw [Real.sqrt_mul (mul_nonneg ((K.law h batch fresh).nonneg path.1)
        ((L.law h batch fresh).nonneg path.1)), ih path.1 path.2]
      rw [← FinDist.midpoint_factorization (K.law h batch fresh) (L.law h batch fresh)
        (K.positive h batch fresh) (L.positive h batch fresh) path.1]
      ring

/-- Full adaptive affinity identity on actual program executions. -/
theorem retained_affinity_eq_midpoint_expectation (O : FrozenOracle N V)
    (K L : BatchKernel N V) {h : History N V} (p : Program N V h) :
    FinDist.affinity (retainedLaw O K p) (retainedLaw O L p) =
      ∑ path, retainedLaw O (K.midpoint L) p path *
        retainedAffinityWeight O K L p path := by
  exact Finset.sum_congr rfl (fun path _ ↦ retained_mass_factorization O K L p path)

/-- The actual program's retained-path Hellinger loss is its midpoint loss. -/
theorem retained_sqHellinger_eq_midpoint_loss (O : FrozenOracle N V)
    (K L : BatchKernel N V) {h : History N V} (p : Program N V h) :
    FinDist.sqHellinger (retainedLaw O K p) (retainedLaw O L p) =
      ∑ path, retainedLaw O (K.midpoint L) p path *
        (1 - retainedAffinityWeight O K L p path) := by
  rw [FinDist.sqHellinger, retained_affinity_eq_midpoint_expectation]
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, (retainedLaw O (K.midpoint L) p).sum_mass]

/-- The output law induced by a retained execution. -/
def retainedOutputLaw (O : FrozenOracle N V) (K : BatchKernel N V)
    {h : History N V} (p : Program N V h) : FinDist (Configuration N V) :=
  (retainedLaw O K p).map (retainedOutput O p)

/-- The proved replay equivalence transfers the midpoint identity from paths
to the actual complete outputs, with no injectivity assumption left to supply. -/
theorem output_sqHellinger_eq_midpoint_loss (O : FrozenOracle N V)
    (K L : BatchKernel N V) (p : Program N V (History.empty N V)) :
    FinDist.sqHellinger (retainedOutputLaw O K p) (retainedOutputLaw O L p) =
      ∑ path, retainedLaw O (K.midpoint L) p path *
        (1 - retainedAffinityWeight O K L p path) := by
  change FinDist.sqHellinger
    ((retainedLaw O K p).map (retainedOutputEquiv O p))
    ((retainedLaw O L p).map (retainedOutputEquiv O p)) = _
  rw [FinDist.sqHellinger_map_equiv, retained_sqHellinger_eq_midpoint_loss]

/-- With oracle-product commit laws, retaining and then forgetting the path
recovers the pre-existing sampler evaluation exactly. -/
theorem retainedOutputLaw_ofOracle (O : FrozenOracle N V)
    {h : History N V} (p : Program N V h) :
    retainedOutputLaw O (BatchKernel.ofOracle O) p = eval O p := by
  induction p with
  | @done h complete =>
      ext x
      change (FinDist.dirac (α := PUnit) PUnit.unit).map
        (fun _ ↦ h.completedConfiguration complete) x =
          FinDist.dirac (h.completedConfiguration complete) x
      rw [FinDist.map_apply]
      simp [FinDist.dirac_apply, eq_comm]
  | query state respects next ih => exact ih (O.readState state)
  | @commit h batch nonempty fresh next ih =>
      change (FinDist.sigmaJoint (O.commitDistribution h batch fresh)
        (fun z ↦ retainedLaw O (BatchKernel.ofOracle O) (next z))).map
          (fun path ↦ retainedOutput O (next path.1) path.2) = _
      rw [FinDist.sigmaJoint_map]
      change (O.commitDistribution h batch fresh).bind
        (fun z ↦ retainedOutputLaw O (BatchKernel.ofOracle O) (next z)) = _
      simp only [ih, eval]

variable [Nonempty V]

/-- The retained exact batch execution agrees with the independently defined
joint-reference evaluator, including all fixed frozen-oracle query replies. -/
theorem retainedOutputLaw_ofTarget (O : FrozenOracle N V)
    (target : FinDist (Configuration N V)) (hpositive : target.StrictlyPositive)
    {h : History N V} (p : Program N V h) :
    retainedOutputLaw O (BatchKernel.ofTarget target hpositive) p =
      evalJointReference target hpositive O p := by
  induction p with
  | @done h complete =>
      ext x
      change (FinDist.dirac (α := PUnit) PUnit.unit).map
        (fun _ ↦ h.completedConfiguration complete) x =
          FinDist.dirac (h.completedConfiguration complete) x
      rw [FinDist.map_apply]
      simp [FinDist.dirac_apply, eq_comm]
  | query state respects next ih => exact ih (O.readState state)
  | @commit h batch nonempty fresh next ih =>
      change (FinDist.sigmaJoint (h.jointBatchLaw target hpositive batch)
        (fun z ↦ retainedLaw O (BatchKernel.ofTarget target hpositive) (next z))).map
          (fun path ↦ retainedOutput O (next path.1) path.2) = _
      rw [FinDist.sigmaJoint_map]
      change (h.jointBatchLaw target hpositive batch).bind
        (fun z ↦ retainedOutputLaw O (BatchKernel.ofTarget target hpositive) (next z)) = _
      simp only [ih, evalJointReference]

/-- The paper's adaptive midpoint identity for an actual sampler program:
the left law is the target and the right law is its frozen-oracle output. -/
theorem target_output_sqHellinger_eq_midpoint_loss (O : FrozenOracle N V)
    (target : FinDist (Configuration N V)) (hpositive : target.StrictlyPositive)
    (p : Program N V (History.empty N V)) :
    FinDist.sqHellinger target (eval O p) =
      ∑ path, retainedLaw O
        ((BatchKernel.ofTarget target hpositive).midpoint (BatchKernel.ofOracle O)) p path *
        (1 - retainedAffinityWeight O (BatchKernel.ofTarget target hpositive)
          (BatchKernel.ofOracle O) p path) := by
  have hidentity := output_sqHellinger_eq_midpoint_loss O
    (BatchKernel.ofTarget target hpositive) (BatchKernel.ofOracle O) p
  rw [retainedOutputLaw_ofTarget, retainedOutputLaw_ofOracle,
    evalJointReference_eq_conditionalLaw, History.conditionalLaw_empty] at hidentity
  exact hidentity

end

end Program

namespace Sampler

variable {N : ℕ} {V : Type u} {Seed : Type v}
variable [Fintype V] [DecidableEq V] [Nonempty V]

noncomputable section

/-- The fixed-seed midpoint law on actual retained program paths. The same
frozen oracle supplies the distinguished preprocessing reply and all probes. -/
def midpointPathLaw (A : Sampler N V Seed) (M : ForestModel N V)
    (w : Seed) (O : FrozenOracle N V) :
    FinDist (Program.RetainedPath O
      (A.program w (O.readState (MaskedState.allMask N V)))) :=
  Program.retainedLaw O
    ((BatchKernel.ofTarget M.target M.target_positive).midpoint (BatchKernel.ofOracle O))
    (A.program w (O.readState (MaskedState.allMask N V)))

/-- Product of the exact-joint versus oracle-product local affinities along
one fixed-seed retained sampler path. -/
def midpointPathWeight (A : Sampler N V Seed) (M : ForestModel N V)
    (w : Seed) (O : FrozenOracle N V)
    (path : Program.RetainedPath O
      (A.program w (O.readState (MaskedState.allMask N V)))) : ℝ :=
  Program.retainedAffinityWeight O (BatchKernel.ofTarget M.target M.target_positive)
    (BatchKernel.ofOracle O) (A.program w (O.readState (MaskedState.allMask N V))) path

/-- Squared Hellinger loss for the existing sampler semantics, expressed as
the expectation of the adaptive midpoint path penalty. -/
theorem output_sqHellinger_eq_midpoint_loss (A : Sampler N V Seed)
    (M : ForestModel N V) (w : Seed) (O : FrozenOracle N V) :
    FinDist.sqHellinger M.target (A.outputLaw w O) =
      ∑ path, A.midpointPathLaw M w O path *
        (1 - A.midpointPathWeight M w O path) :=
  Program.target_output_sqHellinger_eq_midpoint_loss O M.target M.target_positive
    (A.program w (O.readState (MaskedState.allMask N V)))

/-- The paper's fixed-seed adaptive midpoint identity, now instantiated to
the actual sampler, true target, frozen queries, and commit semantics. -/
theorem adaptive_midpoint_identity (A : Sampler N V Seed)
    (M : ForestModel N V) (w : Seed) (O : FrozenOracle N V) :
    1 - FinDist.sqHellinger M.target (A.outputLaw w O) =
      ∑ path, A.midpointPathLaw M w O path *
        A.midpointPathWeight M w O path := by
  have h := A.output_sqHellinger_eq_midpoint_loss M w O
  simp_rw [mul_sub, mul_one] at h
  rw [Finset.sum_sub_distrib, (A.midpointPathLaw M w O).sum_mass] at h
  linarith

end

end Sampler

end ForestSampling
