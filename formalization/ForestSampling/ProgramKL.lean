import ForestSampling.ProgramMidpoint
import ForestSampling.FiniteKL

set_option autoImplicit false

open scoped BigOperators

namespace ForestSampling

/-!
# Forward KL along the actual adaptive sampler

Retained executions have a proved replay equivalence with full outputs. This
module uses that equivalence to transfer the exact finite KL chain rule to the
sampler, then separates batch dependence from singleton oracle error.
-/

namespace Program

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

/-- A real cost attached to each fresh batch at its committed history. -/
abbrev BatchCost (N : ℕ) (V : Type*) [DecidableEq V] :=
  (h : History N V) → (batch : Finset (Position N)) →
    batch ⊆ h.uncommitted → ℝ

/-- Sum of local batch costs along a retained execution. Probes add no term. -/
def retainedCost (O : FrozenOracle N V) (cost : BatchCost N V) :
    {h : History N V} → (p : Program N V h) → RetainedPath O p → ℝ
  | _, .done _, _ => 0
  | _, .query state _ next, path =>
      retainedCost O cost (next (O.readState state)) path
  | h, .commit batch _ fresh next, path =>
      cost h batch fresh + retainedCost O cost (next path.1) path.2

/-- Positive batch kernels induce positive mass on every retained execution. -/
theorem retainedLaw_strictlyPositive (O : FrozenOracle N V) (K : BatchKernel N V)
    {h : History N V} (p : Program N V h) : (retainedLaw O K p).StrictlyPositive := by
  induction p with
  | done complete =>
      intro path
      cases path
      simp [retainedLaw]
  | query state respects next ih => exact ih (O.readState state)
  | @commit h batch nonempty fresh next ih =>
      exact FinDist.sigmaJoint_strictlyPositive _ _ (K.positive h batch fresh) ih

/-- The exact chain rule on retained executions of the existing program
semantics. Its expectation is under the first, reference batch kernel. -/
theorem retained_klDivergence_eq_expectation (O : FrozenOracle N V)
    (K L : BatchKernel N V) {h : History N V} (p : Program N V h) :
    FinDist.klDivergence (retainedLaw O K p) (retainedLaw O L p) =
      ∑ path, retainedLaw O K p path *
        retainedCost O (fun h b fresh ↦ FinDist.klDivergence
          (K.law h b fresh) (L.law h b fresh)) p path := by
  induction p with
  | done complete =>
      change FinDist.klDivergence (FinDist.dirac (α := PUnit) PUnit.unit)
        (FinDist.dirac PUnit.unit) = ∑ _path : PUnit,
          FinDist.dirac PUnit.unit _path * 0
      simp
  | query state respects next ih => exact ih (O.readState state)
  | @commit h batch nonempty fresh next ih =>
      change FinDist.klDivergence
          (FinDist.sigmaJoint (K.law h batch fresh) (fun z ↦ retainedLaw O K (next z)))
          (FinDist.sigmaJoint (L.law h batch fresh) (fun z ↦ retainedLaw O L (next z))) =
        ∑ path : (z : batch → V) × RetainedPath O (next z),
          FinDist.sigmaJoint (K.law h batch fresh) (fun z ↦ retainedLaw O K (next z)) path *
            (FinDist.klDivergence (K.law h batch fresh) (L.law h batch fresh) +
              retainedCost O (fun h b fresh ↦ FinDist.klDivergence
                (K.law h b fresh) (L.law h b fresh)) (next path.1) path.2)
      rw [FinDist.klDivergence_sigmaJoint _ _ _ _
        (K.positive h batch fresh) (L.positive h batch fresh)
        (fun z ↦ retainedLaw_strictlyPositive O K (next z))
        (fun z ↦ retainedLaw_strictlyPositive O L (next z))]
      simp_rw [ih]
      rw [Fintype.sum_sigma]
      simp only [FinDist.sigmaJoint_apply]
      symm
      calc
        (∑ z, ∑ path,
            (K.law h batch fresh z * retainedLaw O K (next z) path) *
              (FinDist.klDivergence (K.law h batch fresh) (L.law h batch fresh) +
                retainedCost O (fun h b fresh ↦ FinDist.klDivergence
                  (K.law h b fresh) (L.law h b fresh)) (next z) path)) =
            ∑ z, K.law h batch fresh z *
              (FinDist.klDivergence (K.law h batch fresh) (L.law h batch fresh) +
                ∑ path, retainedLaw O K (next z) path *
                  retainedCost O (fun h b fresh ↦ FinDist.klDivergence
                    (K.law h b fresh) (L.law h b fresh)) (next z) path) := by
          apply Finset.sum_congr rfl
          intro z _
          simp_rw [mul_add, mul_assoc, Finset.sum_add_distrib]
          rw [← Finset.mul_sum, ← Finset.sum_mul,
            (retainedLaw O K (next z)).sum_mass, one_mul,
            ← Finset.mul_sum]
        _ = _ := by
          simp_rw [mul_add, Finset.sum_add_distrib]
          rw [← Finset.sum_mul, (K.law h batch fresh).sum_mass, one_mul]

/-- The replay equivalence transfers the chain identity to full outputs.
The equality uses irreversibility of commits, already proved by replay. -/
theorem output_klDivergence_eq_expectation (O : FrozenOracle N V)
    (K L : BatchKernel N V) (p : Program N V (History.empty N V)) :
    FinDist.klDivergence (retainedOutputLaw O K p) (retainedOutputLaw O L p) =
      ∑ path, retainedLaw O K p path *
        retainedCost O (fun h b fresh ↦ FinDist.klDivergence
          (K.law h b fresh) (L.law h b fresh)) p path := by
  change FinDist.klDivergence
    ((retainedLaw O K p).map (retainedOutputEquiv O p))
    ((retainedLaw O L p).map (retainedOutputEquiv O p)) = _
  rw [FinDist.klDivergence_map_equiv, retained_klDivergence_eq_expectation]

/-- Costs add along each path, independently of which adaptive path is taken. -/
theorem retainedCost_add (O : FrozenOracle N V) (cost₁ cost₂ : BatchCost N V)
    {h : History N V} (p : Program N V h) (path : RetainedPath O p) :
    retainedCost O (fun h b fresh ↦ cost₁ h b fresh + cost₂ h b fresh) p path =
      retainedCost O cost₁ p path + retainedCost O cost₂ p path := by
  induction p with
  | done complete => simp [retainedCost]
  | query state respects next ih => exact ih (O.readState state) path
  | @commit h batch nonempty fresh next ih =>
      simp only [retainedCost, ih path.1 path.2]
      ring

/-- A local per-coordinate budget accumulates to the count of remaining
coordinates on every retained path, including unsafe and fallback paths. -/
theorem retainedCost_le_coordinate_budget (O : FrozenOracle N V)
    (cost : BatchCost N V) (budget : ℝ) (hbudget : 0 ≤ budget)
    (hcost : ∀ h b fresh, cost h b fresh ≤ (b.card : ℝ) * budget)
    {h : History N V} (p : Program N V h) (path : RetainedPath O p) :
    retainedCost O cost p path ≤ (h.uncommitted.card : ℝ) * budget := by
  induction p with
  | done complete =>
      simp only [retainedCost]
      positivity
  | query state respects next ih => exact ih (O.readState state) path
  | @commit h batch nonempty fresh next ih =>
      have hchild := ih path.1 path.2
      have hlocal := hcost h batch fresh
      have hcard :
          ((h.appendBatch batch fresh path.1).uncommitted.card : ℝ) + batch.card =
            (h.uncommitted.card : ℝ) := by
        exact_mod_cast h.appendBatch_uncommitted_card_add batch fresh path.1
      change cost h batch fresh + retainedCost O cost (next path.1) path.2 ≤ _
      nlinarith

/-- Nonnegative local costs stay nonnegative on every retained execution. -/
theorem retainedCost_nonneg (O : FrozenOracle N V) (cost : BatchCost N V)
    (hcost : ∀ h b fresh, 0 ≤ cost h b fresh)
    {h : History N V} (p : Program N V h) (path : RetainedPath O p) :
    0 ≤ retainedCost O cost p path := by
  induction p with
  | done complete => exact le_rfl
  | query state respects next ih => exact ih (O.readState state) path
  | @commit h batch nonempty fresh next ih =>
      exact add_nonneg (hcost h batch fresh) (ih path.1 path.2)

variable [Nonempty V]

/-- The conditional total-correlation cost of one actual selected batch. -/
def batchTotalCorrelation (target : FinDist (Configuration N V))
    (hpositive : target.StrictlyPositive) : BatchCost N V :=
  fun h batch _fresh ↦ FinDist.totalCorrelation (h.jointBatchLaw target hpositive batch)

/-- Singleton forward-KL error at the mandatory commit-state rows. -/
def batchRowKL (target : FinDist (Configuration N V))
    (hpositive : target.StrictlyPositive) (O : FrozenOracle N V) : BatchCost N V :=
  fun h batch fresh ↦ ∑ j : batch,
    FinDist.klDivergence
      ((MaskedState.commitState h).exactRow target hpositive
        (FrozenOracle.commitReadout h batch fresh j))
      (O.row (MaskedState.commitState h) (FrozenOracle.commitReadout h batch fresh j))

/-- The actual true-joint versus oracle-product batch KL separates into
total correlation and its exact singleton forward-KL errors. -/
theorem joint_oracle_batch_kl_decomposition
    (target : FinDist (Configuration N V)) (hpositive : target.StrictlyPositive)
    (O : FrozenOracle N V) (h : History N V) (batch : Finset (Position N))
    (fresh : batch ⊆ h.uncommitted) :
    FinDist.klDivergence (h.jointBatchLaw target hpositive batch)
      (O.commitDistribution h batch fresh) =
      batchTotalCorrelation target hpositive h batch fresh +
        batchRowKL target hpositive O h batch fresh := by
  change FinDist.klDivergence (h.jointBatchLaw target hpositive batch)
      (FinDist.piProduct (fun j : batch ↦
        O.row (MaskedState.commitState h) (FrozenOracle.commitReadout h batch fresh j))) = _
  rw [FinDist.klDivergence_piProduct_decomposition _ _
    (h.jointBatchLaw_strictlyPositive target hpositive batch fresh)
    (fun j ↦ O.row_positive _ _)]
  unfold batchTotalCorrelation batchRowKL
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [FinDist.piMarginal, History.jointBatchLaw_map_eval,
    MaskedState.exactRow_commitState]
  rfl

/-- Exact adaptive output-KL decomposition for the actual oracle sampler.
The expectation is under the retained true-joint reference law. -/
theorem target_output_klDivergence_eq_tc_add_rows (O : FrozenOracle N V)
    (target : FinDist (Configuration N V)) (hpositive : target.StrictlyPositive)
    (p : Program N V (History.empty N V)) :
    FinDist.klDivergence target (eval O p) =
      ∑ path, retainedLaw O (BatchKernel.ofTarget target hpositive) p path *
        (retainedCost O (batchTotalCorrelation target hpositive) p path +
          retainedCost O (batchRowKL target hpositive O) p path) := by
  have hidentity := output_klDivergence_eq_expectation O
    (BatchKernel.ofTarget target hpositive) (BatchKernel.ofOracle O) p
  rw [retainedOutputLaw_ofTarget, retainedOutputLaw_ofOracle,
    evalJointReference_eq_conditionalLaw, History.conditionalLaw_empty] at hidentity
  rw [hidentity]
  apply Finset.sum_congr rfl
  intro path _
  congr 1
  have hlocal :
      (fun h b fresh ↦ FinDist.klDivergence
        ((BatchKernel.ofTarget target hpositive).law h b fresh)
        ((BatchKernel.ofOracle O).law h b fresh)) =
      (fun h b fresh ↦ batchTotalCorrelation target hpositive h b fresh +
        batchRowKL target hpositive O h b fresh) := by
    funext h b fresh
    exact joint_oracle_batch_kl_decomposition target hpositive O h b fresh
  rw [hlocal, retainedCost_add]

/-- Every batch dependence cost is bounded without a minimum-atom assumption. -/
theorem batchTotalCorrelation_le (target : FinDist (Configuration N V))
    (hpositive : target.StrictlyPositive) (h : History N V)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted) :
    batchTotalCorrelation target hpositive h batch fresh ≤
      (batch.card : ℝ) * Real.log (Fintype.card V) := by
  simpa only [batchTotalCorrelation, Fintype.card_coe] using
    FinDist.totalCorrelation_le_card_mul_log_card (h.jointBatchLaw target hpositive batch)
      (h.jointBatchLaw_strictlyPositive target hpositive batch fresh)

/-- Uniform singleton accuracy bounds the cost of each batch by its size. -/
theorem batchRowKL_le (target : FinDist (Configuration N V))
    (hpositive : target.StrictlyPositive) (O : FrozenOracle N V) (κ : ℝ)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.klDivergence (y.exactRow target hpositive j) (O.row y j) ≤ κ)
    (h : History N V) (batch : Finset (Position N))
    (fresh : batch ⊆ h.uncommitted) :
    batchRowKL target hpositive O h batch fresh ≤ (batch.card : ℝ) * κ := by
  unfold batchRowKL
  calc
    (∑ j : batch, FinDist.klDivergence
        ((MaskedState.commitState h).exactRow target hpositive
          (FrozenOracle.commitReadout h batch fresh j))
        (O.row (MaskedState.commitState h) (FrozenOracle.commitReadout h batch fresh j))) ≤
        ∑ _j : batch, κ := Finset.sum_le_sum fun j _ ↦ hrows _ _
    _ = _ := by simp

/-- Total dependence cost is at most the residual coordinate count times
log vocabulary size on every path, including failed-screen paths. -/
theorem retainedTotalCorrelation_le (target : FinDist (Configuration N V))
    (hpositive : target.StrictlyPositive) (O : FrozenOracle N V)
    {h : History N V} (p : Program N V h) (path : RetainedPath O p) :
    retainedCost O (batchTotalCorrelation target hpositive) p path ≤
      (h.uncommitted.card : ℝ) * Real.log (Fintype.card V) :=
  retainedCost_le_coordinate_budget O (batchTotalCorrelation target hpositive)
    (Real.log (Fintype.card V)) (Real.log_natCast_nonneg _)
    (batchTotalCorrelation_le target hpositive) p path

/-- Each coordinate is charged once to the row-KL budget on every path. -/
theorem retainedRowKL_le (target : FinDist (Configuration N V))
    (hpositive : target.StrictlyPositive) (O : FrozenOracle N V)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.klDivergence (y.exactRow target hpositive j) (O.row y j) ≤ κ)
    {h : History N V} (p : Program N V h) (path : RetainedPath O p) :
    retainedCost O (batchRowKL target hpositive O) p path ≤
      (h.uncommitted.card : ℝ) * κ :=
  retainedCost_le_coordinate_budget O (batchRowKL target hpositive O) κ hκ
    (batchRowKL_le target hpositive O κ hrows) p path

/-- Along this particular retained path, each true joint batch conditional
factorizes over its singleton marginals. Proving this from graph-based safety
is a separate residual conditional-independence obligation. -/
def PathBatchesFactorize (target : FinDist (Configuration N V))
    (hpositive : target.StrictlyPositive) (O : FrozenOracle N V) :
    {h : History N V} → (p : Program N V h) → RetainedPath O p → Prop
  | _, .done _, _ => True
  | _, .query state _ next, path =>
      PathBatchesFactorize target hpositive O (next (O.readState state)) path
  | h, .commit batch _ _fresh next, path =>
      h.jointBatchLaw target hpositive batch =
          FinDist.piProduct (h.jointBatchLaw target hpositive batch).piMarginal ∧
        PathBatchesFactorize target hpositive O (next path.1) path.2

/-- Conditional factorization at every visited batch eliminates all pathwise
total correlation. This does not assume the implemented graph is correct. -/
theorem retainedTotalCorrelation_eq_zero_of_factorizes
    (target : FinDist (Configuration N V)) (hpositive : target.StrictlyPositive)
    (O : FrozenOracle N V) {h : History N V}
    (p : Program N V h) (path : RetainedPath O p)
    (hfactor : PathBatchesFactorize target hpositive O p path) :
    retainedCost O (batchTotalCorrelation target hpositive) p path = 0 := by
  induction p with
  | done complete => rfl
  | query state respects next ih => exact ih (O.readState state) path hfactor
  | @commit h batch nonempty fresh next ih =>
      change batchTotalCorrelation target hpositive h batch fresh +
        retainedCost O (batchTotalCorrelation target hpositive) (next path.1) path.2 = 0
      rw [ih path.1 path.2 hfactor.2]
      exact add_zero _ |>.trans
        (FinDist.totalCorrelation_eq_zero_of_factorizes _ hfactor.1)

/-- At a fixed seed, charging only nonfactorizing paths yields the finite
reference-failure KL bound. The event probability is under the actual retained
joint reference, so no TV-to-KL conversion or change of measure is used. -/
theorem target_output_klDivergence_le_failure_mass (O : FrozenOracle N V)
    (target : FinDist (Configuration N V)) (hpositive : target.StrictlyPositive)
    (p : Program N V (History.empty N V))
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.klDivergence (y.exactRow target hpositive j) (O.row y j) ≤ κ)
    (bad : RetainedPath O p → Prop) [DecidablePred bad]
    (hgood : ∀ path, ¬ bad path → PathBatchesFactorize target hpositive O p path) :
    FinDist.klDivergence target (eval O p) ≤
      (N : ℝ) * κ + (N : ℝ) * Real.log (Fintype.card V) *
        (retainedLaw O (BatchKernel.ofTarget target hpositive) p).eventMass bad := by
  let ref := retainedLaw O (BatchKernel.ofTarget target hpositive) p
  have hrowPath (path : RetainedPath O p) :
      retainedCost O (batchRowKL target hpositive O) p path ≤ (N : ℝ) * κ := by
    simpa only [History.uncommitted, History.empty_committed, Finset.sdiff_empty,
      Finset.card_univ, Fintype.card_fin] using
      retainedRowKL_le target hpositive O κ hκ hrows p path
  have htcPath (path : RetainedPath O p) :
      retainedCost O (batchTotalCorrelation target hpositive) p path ≤
        if bad path then (N : ℝ) * Real.log (Fintype.card V) else 0 := by
    by_cases hb : bad path
    · simpa only [hb, ite_true, History.uncommitted, History.empty_committed,
        Finset.sdiff_empty, Finset.card_univ, Fintype.card_fin] using
        retainedTotalCorrelation_le target hpositive O p path
    · rw [if_neg hb, retainedTotalCorrelation_eq_zero_of_factorizes
        target hpositive O p path (hgood path hb)]
  rw [target_output_klDivergence_eq_tc_add_rows O target hpositive p]
  calc
    (∑ path, ref path *
        (retainedCost O (batchTotalCorrelation target hpositive) p path +
          retainedCost O (batchRowKL target hpositive O) p path)) ≤
        ∑ path, ref path * ((N : ℝ) * κ +
          if bad path then (N : ℝ) * Real.log (Fintype.card V) else 0) := by
      apply Finset.sum_le_sum
      intro path _
      apply mul_le_mul_of_nonneg_left _ (ref.nonneg path)
      linarith [hrowPath path, htcPath path]
    _ = (N : ℝ) * κ + (N : ℝ) * Real.log (Fintype.card V) * ref.eventMass bad := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, ref.sum_mass, one_mul]
      congr 1
      unfold FinDist.eventMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro path _
      by_cases hb : bad path <;> simp [hb, mul_comm]

end

end Program

namespace Sampler

variable {N : ℕ} {V Seed : Type*}
variable [Fintype V] [DecidableEq V] [Nonempty V]

noncomputable section

/-- Fixed-seed retained path law of the exact joint-reference process. -/
def jointReferencePathLaw (A : Sampler N V Seed) (M : ForestModel N V)
    (w : Seed) (O : FrozenOracle N V) :
    FinDist (Program.RetainedPath O
      (A.program w (O.readState (MaskedState.allMask N V)))) :=
  Program.retainedLaw O (BatchKernel.ofTarget M.target M.target_positive)
    (A.program w (O.readState (MaskedState.allMask N V)))

/-- Sum of conditional batch-dependence costs on one reference execution. -/
def referenceTotalCorrelation (A : Sampler N V Seed) (M : ForestModel N V)
    (w : Seed) (O : FrozenOracle N V)
    (path : Program.RetainedPath O
      (A.program w (O.readState (MaskedState.allMask N V)))) : ℝ :=
  Program.retainedCost O (Program.batchTotalCorrelation M.target M.target_positive)
    (A.program w (O.readState (MaskedState.allMask N V))) path

/-- Sum of exact-to-oracle singleton KL terms on one reference execution. -/
def referenceRowKL (A : Sampler N V Seed) (M : ForestModel N V)
    (w : Seed) (O : FrozenOracle N V)
    (path : Program.RetainedPath O
      (A.program w (O.readState (MaskedState.allMask N V)))) : ℝ :=
  Program.retainedCost O (Program.batchRowKL M.target M.target_positive O)
    (A.program w (O.readState (MaskedState.allMask N V))) path

/-- The manuscript's fixed-seed adaptive joint-reference KL identity,
instantiated to the existing sampler's actual conditional output law. -/
theorem output_klDivergence_eq_reference_expectation (A : Sampler N V Seed)
    (M : ForestModel N V) (w : Seed) (O : FrozenOracle N V) :
    FinDist.klDivergence M.target (A.outputLaw w O) =
      ∑ path, A.jointReferencePathLaw M w O path *
        (A.referenceTotalCorrelation M w O path + A.referenceRowKL M w O path) :=
  Program.target_output_klDivergence_eq_tc_add_rows O M.target M.target_positive
    (A.program w (O.readState (MaskedState.allMask N V)))

/-- All-path dependence-cost bound for the sampler's exact joint reference. -/
theorem referenceTotalCorrelation_le (A : Sampler N V Seed)
    (M : ForestModel N V) (w : Seed) (O : FrozenOracle N V)
    (path : Program.RetainedPath O
      (A.program w (O.readState (MaskedState.allMask N V)))) :
    A.referenceTotalCorrelation M w O path ≤
      (N : ℝ) * Real.log (Fintype.card V) := by
  simpa only [referenceTotalCorrelation, History.uncommitted, History.empty_committed,
    Finset.sdiff_empty, Finset.card_univ, Fintype.card_fin] using
    Program.retainedTotalCorrelation_le M.target M.target_positive O
      (A.program w (O.readState (MaskedState.allMask N V))) path

/-- All-path singleton-error budget for the sampler's exact joint reference. -/
theorem referenceRowKL_le (A : Sampler N V Seed)
    (M : ForestModel N V) (w : Seed) (O : FrozenOracle N V)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.klDivergence (y.exactRow M.target M.target_positive j) (O.row y j) ≤ κ)
    (path : Program.RetainedPath O
      (A.program w (O.readState (MaskedState.allMask N V)))) :
    A.referenceRowKL M w O path ≤ (N : ℝ) * κ := by
  simpa only [referenceRowKL, History.uncommitted, History.empty_committed,
    Finset.sdiff_empty, Finset.card_univ, Fintype.card_fin] using
    Program.retainedRowKL_le M.target M.target_positive O κ hκ hrows
      (A.program w (O.readState (MaskedState.allMask N V))) path

/-- Fixed-seed KL is bounded by the coordinate row budget plus the probability
of a reference path on which conditional batch factorization may fail. -/
theorem output_klDivergence_le_reference_failure_mass (A : Sampler N V Seed)
    (M : ForestModel N V) (w : Seed) (O : FrozenOracle N V)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.klDivergence (y.exactRow M.target M.target_positive j) (O.row y j) ≤ κ)
    (bad : Program.RetainedPath O
      (A.program w (O.readState (MaskedState.allMask N V))) → Prop)
    [DecidablePred bad]
    (hgood : ∀ path, ¬ bad path → Program.PathBatchesFactorize M.target
      M.target_positive O (A.program w (O.readState (MaskedState.allMask N V))) path) :
    FinDist.klDivergence M.target (A.outputLaw w O) ≤
      (N : ℝ) * κ + (N : ℝ) * Real.log (Fintype.card V) *
        (A.jointReferencePathLaw M w O).eventMass bad :=
  Program.target_output_klDivergence_le_failure_mass O M.target M.target_positive
    (A.program w (O.readState (MaskedState.allMask N V))) κ hκ hrows bad hgood

end

end Sampler
end ForestSampling
