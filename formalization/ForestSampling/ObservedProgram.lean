import ForestSampling.OracleBudgets
import ForestSampling.PaperStatements

set_option autoImplicit false
open MeasureTheory

namespace ForestSampling

universe u v

namespace FrozenOracle

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- The probability rows explicitly returned together with a commit's
sampled values in the manuscript's ordinary observation. -/
def commitRows (O : FrozenOracle N V) (h : History N V) (batch : Finset (Position N))
    (fresh : batch ⊆ h.uncommitted) : batch → FinDist V :=
  fun j ↦ O.row (MaskedState.commitState h) (commitReadout h batch fresh j)

end FrozenOracle

/-- The manuscript's finite adaptive protocol including commit feedback.
A batch is selected before its rows are returned. The continuation observes
both those probability rows and the sampled batch values. Query responses
may contain every masked row, which also permits ignoring unrequested rows. -/
inductive ObservedProgram (N : ℕ) (V : Type u) [Fintype V] [DecidableEq V] :
    History N V → Type (u + 1) where
  | done {h : History N V} (complete : h.committed = Finset.univ) : ObservedProgram N V h
  | query {h : History N V} (state : MaskedState N V)
      (respects : state.RespectsHistory h)
      (next : (MaskedPosition state → FinDist V) → ObservedProgram N V h) : ObservedProgram N V h
  | commit {h : History N V} (batch : Finset (Position N))
      (nonempty : batch.Nonempty) (fresh : batch ⊆ h.uncommitted)
      (next : (rows : batch → FinDist V) → (z : batch → V) →
        ObservedProgram N V (h.appendBatch batch fresh z)) : ObservedProgram N V h

namespace ObservedProgram

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- Evaluate the observed protocol with its actual frozen commit feedback
and the same independent product sampling law as the original protocol. -/
noncomputable def eval (O : FrozenOracle N V) :
    {h : History N V} → ObservedProgram N V h → FinDist (Configuration N V)
  | h, .done complete => FinDist.dirac (h.completedConfiguration complete)
  | _, .query state _ next => eval O (next (O.readState state))
  | h, .commit batch _ fresh next =>
      (O.commitDistribution h batch fresh).bind fun z ↦ eval O (next (O.commitRows h batch fresh) z)

/-- Compile the feedback observation to a read-only commit-state query
followed by the already chosen batch. The feedback query must be free in
the lower-bound resource model; it is not an additional charged probe.
Only batch rows, not the extra available rows, are passed to the controller. -/
def compile : {h : History N V} → ObservedProgram N V h → Program N V h
  | _, .done complete => .done complete
  | _, .query state respects next => .query state respects (fun reply ↦ compile (next reply))
  | h, .commit batch nonempty fresh next =>
      .query (MaskedState.commitState h) (MaskedState.commitState_respects h)
        (fun reply ↦ .commit batch nonempty fresh
          (fun z ↦ compile (next (fun j ↦ reply (FrozenOracle.commitReadout h batch fresh j)) z)))

/-- The compilation preserves the actual output distribution exactly for
every frozen oracle. The inserted query reveals data without sampling or
changing the history, and the fixed batch draws are unchanged. -/
theorem eval_compile (O : FrozenOracle N V) {h : History N V} (p : ObservedProgram N V h) :
    Program.eval O p.compile = p.eval O := by
  induction p with
  | done complete => rfl
  | query state respects next ih => exact ih (O.readState state)
  | commit batch nonempty fresh next ih =>
      change (O.commitDistribution _ batch fresh).bind
        (fun z ↦ Program.eval O (next (O.commitRows _ batch fresh) z).compile) = _
      congr 1
      funext z
      exact ih (O.commitRows _ batch fresh) z

/-- Actual-oracle budgets for the manuscript's observed protocol: ordinary
queries spend one probe; commit feedback spends no additional probe. -/
def WithinOracleBudgets (O : FrozenOracle N V) :
    {h : History N V} → ObservedProgram N V h → ℕ → ℕ → Prop
  | _, .done _, _, _ => True
  | _, .query state _ next, Q, R =>
      0 < Q ∧ WithinOracleBudgets O (next (O.readState state)) (Q - 1) R
  | h, .commit batch _ fresh next, Q, R =>
      0 < R ∧ ∀ z, WithinOracleBudgets O (next (O.commitRows h batch fresh) z) Q (R - 1)

end ObservedProgram

/-- A public controller before fixing its seed, with the full ordinary
commit observation retained in its program continuations. -/
structure ObservedSampler (N : ℕ) (V : Type u) [Fintype V] [DecidableEq V]
    (Seed : Type v) where
  program : Seed → (MaskedPosition (MaskedState.allMask N V) → FinDist V) →
    ObservedProgram N V (History.empty N V)

namespace ObservedSampler

variable {N : ℕ} {V : Type u} {Seed : Type v} [Fintype V] [DecidableEq V]

def compile (A : ObservedSampler N V Seed) : Sampler N V Seed where
  program w reply := (A.program w reply).compile

noncomputable def outputLaw (A : ObservedSampler N V Seed) (w : Seed)
    (O : FrozenOracle N V) : FinDist (Configuration N V) :=
  (A.program w (O.readState (MaskedState.allMask N V))).eval O

theorem outputLaw_compile (A : ObservedSampler N V Seed) (w : Seed) (O : FrozenOracle N V) :
    A.compile.outputLaw w O = A.outputLaw w O :=
  ObservedProgram.eval_compile O _

def WithinOracleBudgets (A : ObservedSampler N V Seed) (O : FrozenOracle N V) (Q R : ℕ) : Prop :=
  ∀ w, (A.program w (O.readState (MaskedState.allMask N V))).WithinOracleBudgets O Q R

end ObservedSampler

/-- The same arbitrary controller probability space, now attached to the
full observed protocol instead of discarding commit-row feedback. -/
structure RandomizedObservedSamplerData (N : ℕ) (V : Type u)
    [Fintype V] [DecidableEq V] where
  Seed : Type u
  seedMeasurableSpace : MeasurableSpace Seed
  seedMeasure : Measure Seed
  seedIsProbability : IsProbabilityMeasure seedMeasure
  sampler : ObservedSampler N V Seed

namespace RandomizedObservedSamplerData

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- The compiler preserves the controller seed space and its measure. -/
def compile (A : RandomizedObservedSamplerData N V) : RandomizedSamplerData N V where
  Seed := A.Seed
  seedMeasurableSpace := A.seedMeasurableSpace
  seedMeasure := A.seedMeasure
  seedIsProbability := A.seedIsProbability
  sampler := A.sampler.compile

noncomputable def risk (A : RandomizedObservedSamplerData N V) (I : SamplingInstance N V) : ℝ := by
  letI : MeasurableSpace A.Seed := A.seedMeasurableSpace
  exact ∫ w, FinDist.tv I.model.target (A.sampler.outputLaw w I.oracle) ∂A.seedMeasure

def RiskMeasurableAt (A : RandomizedObservedSamplerData N V) (I : SamplingInstance N V) : Prop := by
  letI : MeasurableSpace A.Seed := A.seedMeasurableSpace
  exact AEStronglyMeasurable
    (fun w ↦ FinDist.tv I.model.target (A.sampler.outputLaw w I.oracle)) A.seedMeasure

/-- Seed-averaged TV risk is unchanged, rather than only bounded, by the
feedback compilation. -/
theorem risk_compile (A : RandomizedObservedSamplerData N V) (I : SamplingInstance N V) :
    A.compile.risk I = A.risk I := by
  unfold RandomizedSamplerData.risk Sampler.seedRisk risk
  simp only [compile, ObservedSampler.outputLaw_compile]
  rfl

/-- The measurability obligation is exactly the same loss function. -/
theorem riskMeasurableAt_compile_iff (A : RandomizedObservedSamplerData N V)
    (I : SamplingInstance N V) : A.compile.RiskMeasurableAt I ↔ A.RiskMeasurableAt I := by
  unfold RandomizedSamplerData.RiskMeasurableAt RiskMeasurableAt
  simp only [compile, ObservedSampler.outputLaw_compile]
  rfl

end RandomizedObservedSamplerData
end ForestSampling
