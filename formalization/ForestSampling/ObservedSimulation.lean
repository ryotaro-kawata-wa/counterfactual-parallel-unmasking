import ForestSampling.ObservedProgram
import ForestSampling.FreeMarginalBudgets

set_option autoImplicit false

namespace ForestSampling

universe u v

namespace ObservedProgram

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- Every paper-budgeted observed program compiles into the stronger free
current-marginal model with the same query and round budgets. The batch
remains fixed before the inserted feedback readout. -/
theorem WithinOracleBudgets.compile_withinFreeMarginalBudgets (O : FrozenOracle N V)
    {h : History N V} {p : ObservedProgram N V h} {Q R : ℕ}
    (hb : p.WithinOracleBudgets O Q R) : p.compile.WithinFreeMarginalBudgets O Q R := by
  induction p generalizing Q R with
  | done complete => trivial
  | @query h state respects next ih =>
      simp only [compile, Program.WithinFreeMarginalBudgets]
      split_ifs
      · exact (ih (O.readState state) hb.2).mono O (Nat.sub_le _ _) le_rfl
      · exact ⟨hb.1, ih (O.readState state) hb.2⟩
  | commit batch nonempty fresh next ih =>
      simp only [compile, Program.WithinFreeMarginalBudgets, if_pos rfl]
      exact ⟨hb.1, fun z ↦ ih (O.commitRows _ batch fresh) z (hb.2 z)⟩

/-- Existing programs embed in the fuller observed interface by ignoring
commit-row feedback. This preserves the established upper constructions. -/
def ofProgram : {h : History N V} → Program N V h → ObservedProgram N V h
  | _, .done complete => .done complete
  | _, .query state respects next => .query state respects (fun reply ↦ ofProgram (next reply))
  | _, .commit batch nonempty fresh next => .commit batch nonempty fresh (fun _ z ↦ ofProgram (next z))

theorem eval_ofProgram (O : FrozenOracle N V) {h : History N V} (p : Program N V h) :
    (ofProgram p).eval O = p.eval O := by
  induction p with
  | done complete => rfl
  | query state respects next ih => exact ih (O.readState state)
  | commit batch nonempty fresh next ih =>
      change (O.commitDistribution _ batch fresh).bind (fun z ↦ (ofProgram (next z)).eval O) = _
      congr 1
      funext z
      exact ih z

theorem withinOracleBudgets_ofProgram (O : FrozenOracle N V)
    {h : History N V} {p : Program N V h} {Q R : ℕ}
    (hb : p.WithinOracleBudgets O Q R) : (ofProgram p).WithinOracleBudgets O Q R := by
  induction p generalizing Q R with
  | done complete => trivial
  | query state respects next ih => exact ⟨hb.1, ih _ hb.2⟩
  | commit batch nonempty fresh next ih => exact ⟨hb.1, fun z ↦ ih z (hb.2 z)⟩

end ObservedProgram

namespace ObservedSampler

variable {N : ℕ} {V : Type u} {Seed : Type v} [Fintype V] [DecidableEq V]

theorem WithinOracleBudgets.compile_withinFreeMarginalBudgets
    {A : ObservedSampler N V Seed} {O : FrozenOracle N V} {Q R : ℕ}
    (hb : A.WithinOracleBudgets O Q R) : A.compile.WithinFreeMarginalBudgets O Q R := by
  intro w
  exact ObservedProgram.WithinOracleBudgets.compile_withinFreeMarginalBudgets O (hb w)

end ObservedSampler

namespace InstanceFamily

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]
variable {ι : Type u} (F : ι → SamplingInstance N V)

/-- The actual admissible sampler class retaining the manuscript's commit
observation, with original probe charges and unchanged seed-risk measurability. -/
def ObservedBudgetedSampler (Q R : ℕ) :=
  {A : RandomizedObservedSamplerData N V //
    (∀ i, A.sampler.WithinOracleBudgets (F i).oracle Q R) ∧ ∀ i, A.RiskMeasurableAt (F i)}

/-- Worst-case seed-averaged TV risk for the full observed protocol. -/
noncomputable def observedWorstCaseRisk (A : RandomizedObservedSamplerData N V) : ℝ :=
  sSup (Set.range fun i ↦ A.risk (F i))

/-- The complete feedback simulation preserves the worst-case risk exactly. -/
theorem worstCaseRisk_compile (A : RandomizedObservedSamplerData N V) :
    worstCaseRisk F A.compile = observedWorstCaseRisk F A := by
  unfold worstCaseRisk observedWorstCaseRisk
  simp only [RandomizedObservedSamplerData.risk_compile]

/-- The original minimax quantifier order, now with all ordinary commit
observations available to the adaptive controller. -/
noncomputable def observedMinimax (Q R : ℕ) : ℝ :=
  sInf (Set.range fun A : ObservedBudgetedSampler F Q R ↦ observedWorstCaseRisk F A.1)

end InstanceFamily
end ForestSampling
