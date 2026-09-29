import ForestSampling.Algorithm

set_option autoImplicit false

open scoped BigOperators

namespace ForestSampling

/-!
# Adaptive Hellinger composition

The query oracle is held fixed while the commit oracle varies. This is the
exact-row hybrid used by the manuscript: replacing query replies as well would
change the controller itself. The composition result below does not require
structural safety; identifying the exact-row hybrid with the target law is a
separate theorem.
-/

namespace FinDist

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Finite mixtures have at least the affinity obtained by retaining the
mixture index. This is the data-processing inequality needed at an adaptive
commit; no disjoint-support hypothesis is required. -/
theorem affinity_bind_ge (p q : FinDist α) (k l : α → FinDist β) :
    (∑ a, Real.sqrt (p a * q a) * affinity (k a) (l a)) ≤
      affinity (p.bind k) (q.bind l) := by
  classical
  have hpoint (b : β) :
      (∑ a, Real.sqrt (p a * q a) * Real.sqrt (k a b * l a b)) ≤
        Real.sqrt ((p.bind k) b * (q.bind l) b) := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset α)
      (fun a ↦ Real.sqrt (p a * k a b))
      (fun a ↦ Real.sqrt (q a * l a b))
    have hleft :
        (∑ a, Real.sqrt (p a * q a) * Real.sqrt (k a b * l a b)) =
          ∑ a, Real.sqrt (p a * k a b) * Real.sqrt (q a * l a b) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Real.sqrt_mul (mul_nonneg (p.nonneg a) (q.nonneg a)),
        ← Real.sqrt_mul (mul_nonneg (p.nonneg a) ((k a).nonneg b))]
      congr 1
      ring
    have hp : (∑ a, Real.sqrt (p a * k a b) ^ 2) = (p.bind k) b := by
      simp only [Real.sq_sqrt (mul_nonneg (p.nonneg _) ((k _).nonneg _)),
        bind_apply]
    have hq : (∑ a, Real.sqrt (q a * l a b) ^ 2) = (q.bind l) b := by
      simp only [Real.sq_sqrt (mul_nonneg (q.nonneg _) ((l _).nonneg _)),
        bind_apply]
    rw [hleft]
    rw [hp, hq, ← Real.sqrt_mul ((p.bind k).nonneg b)] at hcs
    exact hcs
  calc
    (∑ a, Real.sqrt (p a * q a) * affinity (k a) (l a)) =
        ∑ b, ∑ a, Real.sqrt (p a * q a) * Real.sqrt (k a b * l a b) := by
      simp only [affinity, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ affinity (p.bind k) (q.bind l) := by
      exact Finset.sum_le_sum fun b _ ↦ hpoint b

/-- A common upper bound for all child losses adds to the current mixture
loss. The nonnegative remainder is charged only once, even when the next
kernel depends on the current outcome. -/
theorem sqHellinger_bind_le_add (p q : FinDist α) (k l : α → FinDist β)
    (remainder : ℝ) (hremainder : 0 ≤ remainder)
    (hchild : ∀ a, sqHellinger (k a) (l a) ≤ remainder) :
    sqHellinger (p.bind k) (q.bind l) ≤ sqHellinger p q + remainder := by
  have hsum : (1 - remainder) * affinity p q ≤
      ∑ a, Real.sqrt (p a * q a) * affinity (k a) (l a) := by
    unfold affinity
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    have hc : 1 - remainder ≤ affinity (k a) (l a) := by
      have := hchild a
      unfold sqHellinger at this
      linarith
    change (1 - remainder) * Real.sqrt (p a * q a) ≤
      Real.sqrt (p a * q a) * affinity (k a) (l a)
    rw [mul_comm (1 - remainder)]
    exact mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg (p a * q a))
  have hmix := hsum.trans (affinity_bind_ge p q k l)
  have hscale := mul_le_mul_of_nonneg_left (affinity_le_one p q) hremainder
  unfold sqHellinger
  nlinarith

end FinDist

namespace History

variable {N : ℕ} {V : Type*} [DecidableEq V]

/-- Appending a fresh batch removes exactly that batch from the residual set. -/
theorem appendBatch_uncommitted (h : History N V)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted)
    (z : batch → V) :
    (h.appendBatch batch fresh z).uncommitted = h.uncommitted \ batch := by
  ext i
  simp only [mem_uncommitted_iff, appendBatch_committed, Finset.mem_union,
    Finset.mem_sdiff]
  tauto

/-- The current and remaining batch sizes exactly partition the residual
coordinate budget. -/
theorem appendBatch_uncommitted_card_add (h : History N V)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted)
    (z : batch → V) :
    (h.appendBatch batch fresh z).uncommitted.card + batch.card =
      h.uncommitted.card := by
  rw [appendBatch_uncommitted]
  exact Finset.card_sdiff_add_card_eq_card fresh

end History

namespace Program

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Evaluate with fixed frozen replies to every query and a separately
specified oracle for commit draws. The controller and all query responses
are unchanged when only `commitOracle` is replaced. -/
noncomputable def evalWithCommitOracle
    (queryOracle commitOracle : FrozenOracle N V) :
    {h : History N V} → Program N V h → FinDist (Configuration N V)
  | h, .done complete => FinDist.dirac (h.completedConfiguration complete)
  | _h, .query state _respects next =>
      evalWithCommitOracle queryOracle commitOracle
        (next (queryOracle.readState state))
  | h, .commit batch _nonempty fresh next =>
      (commitOracle.commitDistribution h batch fresh).bind fun z ↦
        evalWithCommitOracle queryOracle commitOracle (next z)

/-- Using the same oracle for queries and commits recovers the original
operational semantics. -/
@[simp]
theorem evalWithCommitOracle_self (O : FrozenOracle N V)
    {h : History N V} (p : Program N V h) :
    evalWithCommitOracle O O p = eval O p := by
  induction p with
  | done complete => rfl
  | query state respects next ih =>
      exact ih (O.readState state)
  | commit batch nonempty fresh next ih =>
      simp only [evalWithCommitOracle, eval]
      congr 1
      funext z
      exact ih z

/-- Uniform per-coordinate Hellinger error accumulates over the coordinates
still uncommitted. This theorem allows adaptive query transcripts and batches,
and makes no structural-safety assumption about the hidden forest. -/
theorem sqHellinger_evalWithCommitOracle_le
    (queryOracle leftOracle rightOracle : FrozenOracle N V)
    (rowBudget : ℝ) (hbudget : 0 ≤ rowBudget)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.sqHellinger (leftOracle.row y j) (rightOracle.row y j) ≤ rowBudget)
    {h : History N V} (p : Program N V h) :
    FinDist.sqHellinger
      (evalWithCommitOracle queryOracle leftOracle p)
      (evalWithCommitOracle queryOracle rightOracle p) ≤
      (h.uncommitted.card : ℝ) * rowBudget := by
  induction p with
  | done complete =>
      simp only [evalWithCommitOracle, FinDist.sqHellinger_self]
      positivity
  | query state respects next ih =>
      exact ih (queryOracle.readState state)
  | @commit h batch nonempty fresh next ih =>
      have hlocal : FinDist.sqHellinger
          (leftOracle.commitDistribution h batch fresh)
          (rightOracle.commitDistribution h batch fresh) ≤
          (batch.card : ℝ) * rowBudget := by
        calc
          FinDist.sqHellinger
              (leftOracle.commitDistribution h batch fresh)
              (rightOracle.commitDistribution h batch fresh) ≤
              ∑ j : batch, FinDist.sqHellinger
                (leftOracle.row (MaskedState.commitState h)
                  (FrozenOracle.commitReadout h batch fresh j))
                (rightOracle.row (MaskedState.commitState h)
                  (FrozenOracle.commitReadout h batch fresh j)) :=
            FinDist.sqHellinger_piProduct_le_sum _ _
          _ ≤ ∑ _j : batch, rowBudget :=
            Finset.sum_le_sum fun j _ ↦ hrows _ _
          _ = (batch.card : ℝ) * rowBudget := by simp
      have hremaining : 0 ≤ ((h.uncommitted \ batch).card : ℝ) * rowBudget :=
        mul_nonneg (Nat.cast_nonneg _) hbudget
      have hchild : ∀ z : batch → V,
          FinDist.sqHellinger
            (evalWithCommitOracle queryOracle leftOracle (next z))
            (evalWithCommitOracle queryOracle rightOracle (next z)) ≤
            ((h.uncommitted \ batch).card : ℝ) * rowBudget := by
        intro z
        simpa only [History.appendBatch_uncommitted] using ih z
      have hstep := FinDist.sqHellinger_bind_le_add
        (leftOracle.commitDistribution h batch fresh)
        (rightOracle.commitDistribution h batch fresh)
        (fun z ↦ evalWithCommitOracle queryOracle leftOracle (next z))
        (fun z ↦ evalWithCommitOracle queryOracle rightOracle (next z))
        (((h.uncommitted \ batch).card : ℝ) * rowBudget) hremaining hchild
      have hcard : ((h.uncommitted \ batch).card : ℝ) + batch.card =
          (h.uncommitted.card : ℝ) := by
        exact_mod_cast Finset.card_sdiff_add_card_eq_card fresh
      change FinDist.sqHellinger
        ((leftOracle.commitDistribution h batch fresh).bind
          (fun z ↦ evalWithCommitOracle queryOracle leftOracle (next z)))
        ((rightOracle.commitDistribution h batch fresh).bind
          (fun z ↦ evalWithCommitOracle queryOracle rightOracle (next z))) ≤ _
      nlinarith

/-- The manuscript's exact-row hybrid retains the original frozen query
replies and replaces only product-commit rows by the target's exact rows. -/
noncomputable def exactCommitEval [Nonempty V] (M : ForestModel N V)
    (O : FrozenOracle N V) {h : History N V} (p : Program N V h) :
    FinDist (Configuration N V) :=
  evalWithCommitOracle O (FrozenOracle.exact M) p

/-- The calibrated remaining-coordinate bound for the exact-row hybrid. -/
theorem sqHellinger_exactCommitEval_le [Nonempty V]
    (M : ForestModel N V) (O : FrozenOracle N V) (oracleRadius : ℝ)
    (haccuracy : O.Accurate M oracleRadius)
    {h : History N V} (p : Program N V h) :
    FinDist.sqHellinger (exactCommitEval M O p) (eval O p) ≤
      (h.uncommitted.card : ℝ) * (oracleRadius ^ 2 / (2 * (N : ℝ))) := by
  have hbudget : 0 ≤ oracleRadius ^ 2 / (2 * (N : ℝ)) := by positivity
  simpa only [exactCommitEval, evalWithCommitOracle_self] using
    sqHellinger_evalWithCommitOracle_le O (FrozenOracle.exact M) O
      (oracleRadius ^ 2 / (2 * (N : ℝ))) hbudget
      (fun y j ↦ haccuracy.h2_bound y j) p

end Program

namespace Sampler

variable {N : ℕ} {V Seed : Type*}
variable [Fintype V] [DecidableEq V] [Nonempty V]

/-- Conditional output of the exact-row commit hybrid. Its initial all-mask
reply, subsequent query replies, and controller seed are those of the original
sampler. This law need not equal the target when batches are unsafe. -/
noncomputable def exactCommitOutputLaw (A : Sampler N V Seed)
    (M : ForestModel N V) (w : Seed) (O : FrozenOracle N V) :
    FinDist (Configuration N V) :=
  Program.exactCommitEval M O
    (A.program w (O.readState (MaskedState.allMask N V)))

/-- Adaptive Hellinger composition at the root, with exactly the manuscript's
normalization. Counterfactual queries contribute no coordinate-error charge. -/
theorem sqHellinger_exactCommitOutputLaw_le (A : Sampler N V Seed)
    (M : ForestModel N V) (w : Seed) (O : FrozenOracle N V)
    (oracleRadius : ℝ) (hN : 0 < N) (haccuracy : O.Accurate M oracleRadius) :
    FinDist.sqHellinger (A.exactCommitOutputLaw M w O) (A.outputLaw w O) ≤
      oracleRadius ^ 2 / 2 := by
  have hroot := Program.sqHellinger_exactCommitEval_le M O oracleRadius haccuracy
    (A.program w (O.readState (MaskedState.allMask N V)))
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  calc
    FinDist.sqHellinger (A.exactCommitOutputLaw M w O) (A.outputLaw w O) ≤
        (N : ℝ) * (oracleRadius ^ 2 / (2 * (N : ℝ))) := by
      simpa only [exactCommitOutputLaw, outputLaw, History.uncommitted,
        History.empty_committed, Finset.sdiff_empty, Finset.card_univ,
        Fintype.card_fin] using hroot
    _ = oracleRadius ^ 2 / 2 := by field_simp

/-- The exact-row hybrid and oracle sampler are within the public radius in
TV, for every fixed controller seed. Target accuracy still requires the
separate structural-safety identification of the hybrid with the target. -/
theorem tv_exactCommitOutputLaw_le (A : Sampler N V Seed)
    (M : ForestModel N V) (w : Seed) (O : FrozenOracle N V)
    (oracleRadius : ℝ) (hN : 0 < N) (haccuracy : O.Accurate M oracleRadius) :
    FinDist.tv (A.exactCommitOutputLaw M w O) (A.outputLaw w O) ≤ oracleRadius := by
  calc
    FinDist.tv (A.exactCommitOutputLaw M w O) (A.outputLaw w O) ≤
        Real.sqrt (2 * FinDist.sqHellinger
          (A.exactCommitOutputLaw M w O) (A.outputLaw w O)) :=
      FinDist.tv_le_sqrt_two_mul_sqHellinger _ _
    _ ≤ Real.sqrt (2 * (oracleRadius ^ 2 / 2)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
        (A.sqHellinger_exactCommitOutputLaw_le M w O oracleRadius hN haccuracy)
        (by norm_num))
    _ = oracleRadius := by
      rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
      exact Real.sqrt_sq haccuracy.1

end Sampler

end ForestSampling
