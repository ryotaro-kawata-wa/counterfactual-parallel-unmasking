import ForestSampling.Minimax
import ForestSampling.OracleBudgets
import ForestSampling.HardMidpoint

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling

universe u

namespace InstanceFamily

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]
variable {ι : Type u} (F : ι → SamplingInstance N V)

/-- Samplers obeying the pathwise budgets on each actual family oracle,
including that oracle's actual preprocessing reply, with measurable TV risk. -/
def OracleBudgetedSampler (Q R : ℕ) :=
  {A : RandomizedSamplerData N V //
    (∀ i, A.sampler.WithinOracleBudgets (F i).oracle Q R) ∧
      ∀ i, A.RiskMeasurableAt (F i)}

/-- The manuscript's minimax interface: infimize the same actual seed-averaged
worst-case TV risk over samplers budgeted on every family oracle. -/
noncomputable def oracleMinimax (Q R : ℕ) : ℝ :=
  sInf (Set.range fun A : OracleBudgetedSampler F Q R ↦ worstCaseRisk F A.1)

/-- A universal-reply budget supplies an actual-oracle budget without changing
the sampler, its seed law, or any risk. -/
def BudgetedSampler.toOracleBudgetedSampler {Q R : ℕ} (A : BudgetedSampler F Q R) :
    OracleBudgetedSampler F Q R :=
  ⟨A.1, (fun i ↦ Sampler.WithinBudgets.withinOracleBudgets A.2.1 (F i).oracle), A.2.2⟩

@[simp]
theorem BudgetedSampler.toOracleBudgetedSampler_val {Q R : ℕ} (A : BudgetedSampler F Q R) :
    (A.toOracleBudgetedSampler F).1 = A.1 := rfl

/-- One round makes the actual-oracle feasible class nonempty, using the
explicit all-at-once sampler and its original measurable risk. -/
theorem oracleBudgetedSampler_nonempty (Q R : ℕ) (hR : 1 ≤ R) :
    Nonempty (OracleBudgetedSampler F Q R) := by
  obtain ⟨A⟩ := budgetedSampler_nonempty F Q R hR
  exact ⟨A.toOracleBudgetedSampler F⟩

/-- At length zero, no commit round is needed even in the actual-oracle class. -/
theorem oracleBudgetedSampler_zero_nonempty {ι : Type u}
    (F : ι → SamplingInstance 0 V) (Q R : ℕ) :
    Nonempty (OracleBudgetedSampler F Q R) := by
  obtain ⟨A⟩ := budgetedSampler_zero_nonempty F Q R
  exact ⟨A.toOracleBudgetedSampler F⟩

/-- Pointwise worst-case lower bounds pass to the actual-oracle minimax
infimum, retaining the nonemptiness condition on its real-valued range. -/
theorem le_oracleMinimax_of_forall_worstCaseRisk (Q R : ℕ) (c : ℝ)
    (hne : Nonempty (OracleBudgetedSampler F Q R))
    (hlower : ∀ A : OracleBudgetedSampler F Q R, c ≤ worstCaseRisk F A.1) :
    c ≤ oracleMinimax F Q R := by
  let := hne
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨A, rfl⟩
  exact hlower A

/-- The positive-round version supplies the explicit feasible sampler. -/
theorem le_oracleMinimax_of_forall_worstCaseRisk_of_one_le_rounds
    (Q R : ℕ) (hR : 1 ≤ R) (c : ℝ)
    (hlower : ∀ A : OracleBudgetedSampler F Q R, c ≤ worstCaseRisk F A.1) :
    c ≤ oracleMinimax F Q R :=
  le_oracleMinimax_of_forall_worstCaseRisk F Q R c
    (oracleBudgetedSampler_nonempty F Q R hR) hlower

/-- A sampler-dependent adversarial instance suffices in the larger class. -/
theorem le_oracleMinimax_of_forall_exists_risk (Q R : ℕ) (c : ℝ)
    (hne : Nonempty (OracleBudgetedSampler F Q R))
    (hlower : ∀ A : OracleBudgetedSampler F Q R, ∃ i, c ≤ A.1.risk (F i)) :
    c ≤ oracleMinimax F Q R := by
  apply le_oracleMinimax_of_forall_worstCaseRisk F Q R c hne
  intro A
  obtain ⟨i, hi⟩ := hlower A
  exact hi.trans (risk_le_worstCaseRisk F A.1 A.2.2 i)

/-- All risks in the new infimum are bounded below by zero. -/
theorem oracleWorstCaseRisk_range_bddBelow [Nonempty ι] (Q R : ℕ) :
    BddBelow (Set.range fun A : OracleBudgetedSampler F Q R ↦ worstCaseRisk F A.1) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨A, rfl⟩
  exact worstCaseRisk_nonneg F A.1 A.2.2

/-- Any feasible sampler gives an upper bound on the same actual risk infimum. -/
theorem oracleMinimax_le_worstCaseRisk [Nonempty ι] (Q R : ℕ)
    (A : OracleBudgetedSampler F Q R) : oracleMinimax F Q R ≤ worstCaseRisk F A.1 :=
  csInf_le (oracleWorstCaseRisk_range_bddBelow F Q R) (Set.mem_range_self A)

/-- The actual-oracle minimax risk is nonnegative for inhabited index classes. -/
theorem oracleMinimax_nonneg [Nonempty ι] (Q R : ℕ)
    (hne : Nonempty (OracleBudgetedSampler F Q R)) : 0 ≤ oracleMinimax F Q R := by
  apply le_oracleMinimax_of_forall_worstCaseRisk F Q R 0 hne
  intro A
  exact worstCaseRisk_nonneg F A.1 A.2.2

/-- The actual-oracle minimax TV risk is at most one. -/
theorem oracleMinimax_le_one [Nonempty ι] (Q R : ℕ)
    (hne : Nonempty (OracleBudgetedSampler F Q R)) : oracleMinimax F Q R ≤ 1 := by
  obtain ⟨A⟩ := hne
  exact (oracleMinimax_le_worstCaseRisk F Q R A).trans (worstCaseRisk_le_one F A.1 A.2.2)

/-- Enlarging the feasible class from universal replies to actual family
oracles can only decrease minimax risk. This does not transfer an old lower
bound in the opposite direction. -/
theorem oracleMinimax_le_minimax [Nonempty ι] (Q R : ℕ)
    (hne : Nonempty (BudgetedSampler F Q R)) : oracleMinimax F Q R ≤ minimax F Q R := by
  apply le_minimax_of_forall_worstCaseRisk F Q R _ hne
  intro A
  exact oracleMinimax_le_worstCaseRisk F Q R (A.toOracleBudgetedSampler F)

section FinitePrior

variable [Fintype ι]

/-- A finite-prior TV lower bound for every seed of every actual-oracle
budgeted sampler survives seed integration and the minimax infimum. Only the
same stored TV measurability is used; the risk is unchanged. -/
theorem le_oracleMinimax_of_seedwise_prior (π : FinDist ι) (Q R : ℕ) (c : ℝ)
    (hne : Nonempty (OracleBudgetedSampler F Q R))
    (hlower : ∀ A : OracleBudgetedSampler F Q R, ∀ w : A.1.Seed,
      c ≤ ∑ i, π i * FinDist.tv (F i).model.target
        (A.1.sampler.outputLaw w (F i).oracle)) :
    c ≤ oracleMinimax F Q R := by
  apply le_oracleMinimax_of_forall_worstCaseRisk F Q R c hne
  intro A
  exact (le_priorRisk_of_seedwise F π A.1 A.2.2 c (hlower A)).trans
    (priorRisk_le_worstCaseRisk F π A.1 A.2.2)

/-- Positive rounds supply the feasible-class nonemptiness required by the
finite-prior bridge for the manuscript's oracle-indexed budget semantics. -/
theorem le_oracleMinimax_of_seedwise_prior_of_one_le_rounds
    (π : FinDist ι) (Q R : ℕ) (hR : 1 ≤ R) (c : ℝ)
    (hlower : ∀ A : OracleBudgetedSampler F Q R, ∀ w : A.1.Seed,
      c ≤ ∑ i, π i * FinDist.tv (F i).model.target
        (A.1.sampler.outputLaw w (F i).oracle)) :
    c ≤ oracleMinimax F Q R :=
  le_oracleMinimax_of_seedwise_prior F π Q R c
    (oracleBudgetedSampler_nonempty F Q R hR) hlower

end FinitePrior
end InstanceFamily

namespace NonlinearMatchingParameters

variable {N : ℕ}

/-- The actual midpoint penalty implies a lower bound for the manuscript's
larger actual-oracle-budgeted sampler class, through unchanged seedwise TV. -/
theorem le_oracleMinimax_of_midpoint_penalty (P : NonlinearMatchingParameters N)
    (Q R : ℕ) (hR : 1 ≤ R) (c : ℝ)
    (hpenalty : ∀ A : InstanceFamily.OracleBudgetedSampler P.hardFamily Q R,
      ∀ w : A.1.Seed,
      c ≤ ∑ outcome, P.midpointJoint A.1.sampler w outcome *
        P.midpointPenalty A.1.sampler w outcome) :
    c ≤ InstanceFamily.oracleMinimax P.hardFamily Q R := by
  apply InstanceFamily.le_oracleMinimax_of_seedwise_prior_of_one_le_rounds
    P.hardFamily P.instancePrior Q R hR c
  intro A w
  exact (hpenalty A w).trans (P.midpoint_penalty_le_prior_tv A.1.sampler w)

end NonlinearMatchingParameters
end ForestSampling
