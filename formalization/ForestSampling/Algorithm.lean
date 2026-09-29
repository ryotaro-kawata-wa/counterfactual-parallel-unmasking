import ForestSampling.Oracle

set_option autoImplicit false

open scoped BigOperators
open MeasureTheory

namespace ForestSampling

universe u v

namespace History

variable {N : ℕ} {V : Type u} [DecidableEq V]

/-- The initial history has no committed coordinates. -/
def empty (N : ℕ) (V : Type u) : History N V where
  committed := ∅
  value i := False.elim (Finset.notMem_empty i.1 i.2)

@[simp]
theorem empty_committed : (empty N V).committed = ∅ := rfl

/-- Append a fresh batch of realized values to a history. -/
def appendBatch (h : History N V) (batch : Finset (Position N))
    (_fresh : batch ⊆ h.uncommitted) (z : batch → V) : History N V where
  committed := h.committed ∪ batch
  value i := if hi : i.1 ∈ h.committed then h.value ⟨i.1, hi⟩
    else z ⟨i.1, by
      have hiUnion : i.1 ∈ h.committed ∪ batch := i.2
      exact (Finset.mem_union.mp hiUnion).resolve_left hi⟩

@[simp]
theorem appendBatch_committed (h : History N V)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted)
    (z : batch → V) :
    (h.appendBatch batch fresh z).committed = h.committed ∪ batch := rfl

theorem committed_subset_appendBatch (h : History N V)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted)
    (z : batch → V) :
    h.committed ⊆ (h.appendBatch batch fresh z).committed := by
  intro i hi
  exact Finset.mem_union_left batch hi

theorem batch_disjoint_committed (h : History N V)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted) :
    Disjoint h.committed batch := by
  rw [Finset.disjoint_left]
  intro i hiCommitted hiBatch
  have hiUncommitted := fresh hiBatch
  exact (h.mem_uncommitted_iff i).mp hiUncommitted hiCommitted

@[simp]
theorem appendBatch_value_old (h : History N V)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted)
    (z : batch → V) (i : h.committed) :
    (h.appendBatch batch fresh z).value
      ⟨i.1, Finset.mem_union_left batch i.2⟩ = h.value i := by
  simp [appendBatch, i.2]

@[simp]
theorem appendBatch_value_new (h : History N V)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted)
    (z : batch → V) (i : batch) :
    (h.appendBatch batch fresh z).value
      ⟨i.1, Finset.mem_union_right h.committed i.2⟩ = z i := by
  have hiNotCommitted : i.1 ∉ h.committed := by
    exact (h.mem_uncommitted_iff i.1).mp (fresh i.2)
  simp [appendBatch, hiNotCommitted]

/-- Read the unique complete assignment from a terminal history. -/
def completedConfiguration (h : History N V)
    (complete : h.committed = Finset.univ) : Configuration N V :=
  fun i ↦ h.value ⟨i, by rw [complete]; simp⟩

end History

namespace FrozenOracle

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- Evidence that a fresh batch coordinate is masked in the mandatory commit state. -/
def commitReadout (h : History N V) (batch : Finset (Position N))
    (fresh : batch ⊆ h.uncommitted) (j : batch) :
    MaskedPosition (MaskedState.commitState h) :=
  ⟨j.1, (MaskedState.commitState_masked_iff h j.1).2
    ((h.mem_uncommitted_iff j.1).1 (fresh j.2))⟩

/-- The independent product law used for one commit batch. -/
noncomputable def commitDistribution (O : FrozenOracle N V)
    (h : History N V) (batch : Finset (Position N))
    (fresh : batch ⊆ h.uncommitted) : FinDist (batch → V) :=
  FinDist.piProduct fun j : batch ↦
    O.row (MaskedState.commitState h) (commitReadout h batch fresh j)

@[simp]
theorem commitDistribution_apply (O : FrozenOracle N V)
    (h : History N V) (batch : Finset (Position N))
    (fresh : batch ⊆ h.uncommitted) (z : batch → V) :
    O.commitDistribution h batch fresh z =
      ∏ j : batch,
        O.row (MaskedState.commitState h)
          (commitReadout h batch fresh j) (z j) := rfl

end FrozenOracle

/-- A finite, adaptive, no-remasking sampler program at history `h`.

* `query` submits one state and receives all of its masked rows at once;
* `commit` samples a nonempty fresh batch from the product of commit-state rows;
* `done` is available only once all positions have been committed.

Thus counterfactual query responses cannot themselves become committed values,
and commits cannot be rejected or remasked.
-/
inductive Program (N : ℕ) (V : Type u) [Fintype V] [DecidableEq V] :
    History N V → Type (u + 1) where
  | done {h : History N V} (complete : h.committed = Finset.univ) :
      Program N V h
  | query {h : History N V} (state : MaskedState N V)
      (respects : state.RespectsHistory h)
      (next : (MaskedPosition state → FinDist V) → Program N V h) :
      Program N V h
  | commit {h : History N V} (batch : Finset (Position N))
      (nonempty : batch.Nonempty) (fresh : batch ⊆ h.uncommitted)
      (next : (z : batch → V) → Program N V (h.appendBatch batch fresh z)) :
      Program N V h

namespace Program

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- Evaluate a program against a fixed oracle, integrating all commit draws. -/
noncomputable def eval (O : FrozenOracle N V) :
    {h : History N V} → Program N V h → FinDist (Configuration N V)
  | h, .done complete => FinDist.dirac (h.completedConfiguration complete)
  | _h, .query state _respects next => eval O (next (O.readState state))
  | h, .commit batch _nonempty fresh next =>
      (O.commitDistribution h batch fresh).bind fun z ↦ eval O (next z)

/-- Every realized path uses at most `queryBudget` counterfactual submissions
and at most `roundBudget` nonempty commit batches. -/
def WithinBudgets :
    {h : History N V} → Program N V h → ℕ → ℕ → Prop
  | _, .done _, _, _ => True
  | _, .query _ _ next, queryBudget, roundBudget =>
      0 < queryBudget ∧
        ∀ reply, WithinBudgets (next reply) (queryBudget - 1) roundBudget
  | _, .commit _ _ _ next, queryBudget, roundBudget =>
      0 < roundBudget ∧
        ∀ z, WithinBudgets (next z) queryBudget (roundBudget - 1)

theorem withinBudgets_done {h : History N V}
    (complete : h.committed = Finset.univ) (Q R : ℕ) :
    WithinBudgets (.done complete : Program N V h) Q R :=
  True.intro

end Program

/-- A randomized sampler before fixing its controller seed.

The distinguished all-mask reply is supplied once outside `Program`, hence is
not included in `Program.WithinBudgets`; a reported charge can be added
separately.  `Seed` may be an arbitrary probability space.
-/
structure Sampler (N : ℕ) (V : Type u) [Fintype V] [DecidableEq V]
    (Seed : Type v) where
  program : Seed →
    (MaskedPosition (MaskedState.allMask N V) → FinDist V) →
    Program N V (History.empty N V)

namespace Sampler

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]
variable {Seed : Type v}

/-- Conditional output law after fixing the controller seed. -/
noncomputable def outputLaw (A : Sampler N V Seed) (w : Seed)
    (O : FrozenOracle N V) : FinDist (Configuration N V) :=
  Program.eval O <| A.program w (O.readState (MaskedState.allMask N V))

/-- Uniform pathwise resource bounds, including all possible oracle replies. -/
def WithinBudgets (A : Sampler N V Seed) (Q R : ℕ) : Prop :=
  ∀ (w : Seed)
    (preprocessingReply : MaskedPosition (MaskedState.allMask N V) → FinDist V),
    Program.WithinBudgets (A.program w preprocessingReply) Q R

/-- Seed-averaged TV risk.  The TV is taken before averaging over seeds. -/
noncomputable def seedRisk [MeasurableSpace Seed] (μ : Measure Seed)
    (A : Sampler N V Seed) (M : ForestModel N V) (O : FrozenOracle N V) : ℝ :=
  ∫ w, FinDist.tv M.target (A.outputLaw w O) ∂μ

/-- Measurability condition needed for the preceding integral to be a genuine
expectation for every oracle in the accuracy class. -/
def RiskMeasurable [MeasurableSpace Seed] (μ : Measure Seed)
    [Nonempty V] (A : Sampler N V Seed) (M : ForestModel N V)
    (oracleRadius : ℝ) : Prop :=
  ∀ O : FrozenOracle.Class M oracleRadius,
    AEStronglyMeasurable
      (fun w ↦ FinDist.tv M.target (A.outputLaw w O.1)) μ

/-- Oracle-robust seed risk, with the oracle chosen after the target law. -/
noncomputable def robustRisk [MeasurableSpace Seed] (μ : Measure Seed)
    [Nonempty V] (A : Sampler N V Seed) (M : ForestModel N V)
    (oracleRadius : ℝ) : ℝ :=
  sSup (Set.range fun O : FrozenOracle.Class M oracleRadius ↦
    A.seedRisk μ M O.1)

/-- Optional charge for the one distinguished all-mask preprocessing state. -/
def reportedQueries (counterfactualQueries : ℕ) (chargePreprocessing : Bool) : ℕ :=
  counterfactualQueries + if chargePreprocessing then 1 else 0

end Sampler

end ForestSampling
