import ForestSampling.PaperStatements

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace ForestSampling

universe u v

/-!
# Well-defined finite minimax risks

The Bochner integral used for seed risk is a genuine expectation whenever the
seedwise TV loss is a.e. strongly measurable: the loss is bounded by one on a
probability space.  The order-theoretic arguments below retain the nonemptiness
hypotheses required by real-valued `sSup` and `sInf`.
-/

namespace Sampler

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]
variable {Seed : Type v} [MeasurableSpace Seed]
variable (μ : Measure Seed) [IsProbabilityMeasure μ]

/-- Measurable seedwise TV loss is integrable because it lies in `[0, 1]`. -/
theorem integrable_seed_loss (A : Sampler N V Seed)
    (M : ForestModel N V) (O : FrozenOracle N V)
    (hmeas : AEStronglyMeasurable
      (fun w ↦ FinDist.tv M.target (A.outputLaw w O)) μ) :
    Integrable (fun w ↦ FinDist.tv M.target (A.outputLaw w O)) μ := by
  refine (integrable_const (1 : ℝ)).mono' hmeas ?_
  exact ae_of_all _ fun w ↦ by
    rw [Real.norm_of_nonneg (FinDist.tv_nonneg _ _)]
    exact FinDist.tv_le_one _ _

omit [IsProbabilityMeasure μ] in
/-- The seed-averaged TV risk is nonnegative. -/
theorem seedRisk_nonneg (A : Sampler N V Seed)
    (M : ForestModel N V) (O : FrozenOracle N V) :
    0 ≤ A.seedRisk μ M O := by
  exact integral_nonneg fun _ ↦ FinDist.tv_nonneg _ _

/-- Measurable seed-averaged TV risk is at most one. -/
theorem seedRisk_le_one (A : Sampler N V Seed)
    (M : ForestModel N V) (O : FrozenOracle N V)
    (hmeas : AEStronglyMeasurable
      (fun w ↦ FinDist.tv M.target (A.outputLaw w O)) μ) :
    A.seedRisk μ M O ≤ 1 := by
  have hle := integral_mono (integrable_seed_loss μ A M O hmeas)
    (integrable_const (1 : ℝ)) (fun w ↦ FinDist.tv_le_one M.target (A.outputLaw w O))
  simpa [seedRisk] using hle

end Sampler

namespace Program

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- Commit all positions independently in one batch; an empty sequence terminates
without a commit.  This program ignores all counterfactual and preprocessing
information and therefore supplies a feasible baseline for minimax infima. -/
def allAtOnce (N : ℕ) (V : Type u) [Fintype V] [DecidableEq V] :
    Program N V (History.empty N V) := by
  by_cases hN : N = 0
  · refine .done ?_
    subst N
    ext i
    exact Fin.elim0 i
  · refine .commit Finset.univ ?_ ?_ (fun z ↦ .done ?_)
    · exact ⟨⟨0, Nat.pos_of_ne_zero hN⟩, Finset.mem_univ _⟩
    · intro i _
      simp [History.uncommitted]
    · simp

/-- The baseline program satisfies any nonnegative query budget and at least
one available commit round, uniformly over every realized batch. -/
theorem allAtOnce_withinBudgets (Q R : ℕ) (hR : 1 ≤ R) :
    (allAtOnce N V).WithinBudgets Q R := by
  unfold allAtOnce
  split
  · trivial
  · exact ⟨Nat.zero_lt_of_lt hR, fun _ ↦ True.intro⟩

/-- Empty sequences require neither queries nor commit rounds. -/
theorem allAtOnce_zero_withinBudgets (Q R : ℕ) :
    (allAtOnce 0 V).WithinBudgets Q R := by
  simp [allAtOnce, WithinBudgets]

end Program

namespace RandomizedSamplerData

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- Packaged probability-space risk remains nonnegative. -/
theorem risk_nonneg (A : RandomizedSamplerData N V) (I : SamplingInstance N V) :
    0 ≤ A.risk I := by
  let : MeasurableSpace A.Seed := A.seedMeasurableSpace
  let : IsProbabilityMeasure A.seedMeasure := A.seedIsProbability
  exact A.sampler.seedRisk_nonneg A.seedMeasure I.model I.oracle

/-- A measurable packaged risk is bounded by one. -/
theorem risk_le_one (A : RandomizedSamplerData N V) (I : SamplingInstance N V)
    (hmeas : A.RiskMeasurableAt I) : A.risk I ≤ 1 := by
  let : MeasurableSpace A.Seed := A.seedMeasurableSpace
  let : IsProbabilityMeasure A.seedMeasure := A.seedIsProbability
  exact A.sampler.seedRisk_le_one A.seedMeasure I.model I.oracle hmeas

/-- A deterministic controller, represented by a singleton seed probability
space, executes the all-at-once baseline program. -/
noncomputable def allAtOnce (N : ℕ) (V : Type u) [Fintype V] [DecidableEq V] :
    RandomizedSamplerData N V := by
  letI : MeasurableSpace (ULift.{u} Unit) := ⊤
  exact {
    Seed := ULift.{u} Unit
    seedMeasurableSpace := inferInstance
    seedMeasure := Measure.dirac (ULift.up ())
    seedIsProbability := inferInstance
    sampler := { program := fun _ _ ↦ Program.allAtOnce N V }
  }

/-- The singleton seed makes the baseline risk constant, hence measurable for
 every target/oracle instance without any assumption on that instance. -/
theorem allAtOnce_riskMeasurableAt (I : SamplingInstance N V) :
    (allAtOnce N V).RiskMeasurableAt I := by
  dsimp only [RiskMeasurableAt, allAtOnce, Sampler.outputLaw]
  exact aestronglyMeasurable_const

/-- The packaged baseline respects the pathwise budgets. -/
theorem allAtOnce_withinBudgets (Q R : ℕ) (hR : 1 ≤ R) :
    (allAtOnce N V).WithinBudgets Q R := by
  intro _ _
  exact Program.allAtOnce_withinBudgets Q R hR

/-- For length zero the packaged baseline needs no commit round. -/
theorem allAtOnce_zero_withinBudgets (Q R : ℕ) :
    (allAtOnce 0 V).WithinBudgets Q R := by
  intro _ _
  exact Program.allAtOnce_zero_withinBudgets Q R

end RandomizedSamplerData

namespace InstanceFamily

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]
variable {ι : Type u} (F : ι → SamplingInstance N V)

/-- The risks defining a worst case are bounded above by one. -/
theorem risk_range_bddAbove (A : RandomizedSamplerData N V)
    (hmeas : ∀ i, A.RiskMeasurableAt (F i)) :
    BddAbove (Set.range fun i ↦ A.risk (F i)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact A.risk_le_one (F i) (hmeas i)

/-- Any individual instance risk lies below the family's worst-case risk. -/
theorem risk_le_worstCaseRisk (A : RandomizedSamplerData N V)
    (hmeas : ∀ i, A.RiskMeasurableAt (F i)) (i : ι) :
    A.risk (F i) ≤ worstCaseRisk F A := by
  exact le_csSup (risk_range_bddAbove F A hmeas) (Set.mem_range_self i)

/-- A nonempty family's worst-case risk is nonnegative. -/
theorem worstCaseRisk_nonneg [Nonempty ι] (A : RandomizedSamplerData N V)
    (hmeas : ∀ i, A.RiskMeasurableAt (F i)) : 0 ≤ worstCaseRisk F A := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact (A.risk_nonneg (F i)).trans (risk_le_worstCaseRisk F A hmeas i)

/-- A nonempty family's measurable worst-case risk is at most one. -/
theorem worstCaseRisk_le_one [Nonempty ι] (A : RandomizedSamplerData N V)
    (hmeas : ∀ i, A.RiskMeasurableAt (F i)) : worstCaseRisk F A ≤ 1 := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨i, rfl⟩
  exact A.risk_le_one (F i) (hmeas i)

/-- One commit round is sufficient to make the feasible sampler class nonempty. -/
theorem budgetedSampler_nonempty (Q R : ℕ) (hR : 1 ≤ R) :
    Nonempty (BudgetedSampler F Q R) := by
  exact ⟨⟨RandomizedSamplerData.allAtOnce N V,
    RandomizedSamplerData.allAtOnce_withinBudgets Q R hR,
    fun i ↦ RandomizedSamplerData.allAtOnce_riskMeasurableAt (F i)⟩⟩

/-- At length zero, the feasible class is nonempty even with no commit rounds. -/
theorem budgetedSampler_zero_nonempty {ι : Type u}
    (F : ι → SamplingInstance 0 V) (Q R : ℕ) :
    Nonempty (BudgetedSampler F Q R) := by
  exact ⟨⟨RandomizedSamplerData.allAtOnce 0 V,
    RandomizedSamplerData.allAtOnce_zero_withinBudgets Q R,
    fun i ↦ RandomizedSamplerData.allAtOnce_riskMeasurableAt (F i)⟩⟩

/-- A lower bound for every feasible sampler's worst-case risk passes to the
minimax infimum once its indexing class is known to be nonempty. -/
theorem le_minimax_of_forall_worstCaseRisk (Q R : ℕ) (c : ℝ)
    (hne : Nonempty (BudgetedSampler F Q R))
    (hlower : ∀ A : BudgetedSampler F Q R, c ≤ worstCaseRisk F A.1) :
    c ≤ minimax F Q R := by
  let := hne
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨A, rfl⟩
  exact hlower A

/-- The frequently used positive-round form supplies feasible-class
nonemptiness from the explicit baseline sampler. -/
theorem le_minimax_of_forall_worstCaseRisk_of_one_le_rounds
    (Q R : ℕ) (hR : 1 ≤ R) (c : ℝ)
    (hlower : ∀ A : BudgetedSampler F Q R, c ≤ worstCaseRisk F A.1) :
    c ≤ minimax F Q R := by
  exact le_minimax_of_forall_worstCaseRisk F Q R c
    (budgetedSampler_nonempty F Q R hR) hlower

/-- An adversarial instance may depend on the sampler; this quantifier order is
sufficient for a minimax lower bound. -/
theorem le_minimax_of_forall_exists_risk (Q R : ℕ) (c : ℝ)
    (hne : Nonempty (BudgetedSampler F Q R))
    (hlower : ∀ A : BudgetedSampler F Q R, ∃ i, c ≤ A.1.risk (F i)) :
    c ≤ minimax F Q R := by
  apply le_minimax_of_forall_worstCaseRisk F Q R c hne
  intro A
  obtain ⟨i, hi⟩ := hlower A
  exact hi.trans (risk_le_worstCaseRisk F A.1 A.2.2 i)

/-- The set used in the minimax infimum has a concrete lower bound. -/
theorem worstCaseRisk_range_bddBelow [Nonempty ι] (Q R : ℕ) :
    BddBelow (Set.range fun A : BudgetedSampler F Q R ↦ worstCaseRisk F A.1) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨A, rfl⟩
  exact worstCaseRisk_nonneg F A.1 A.2.2

/-- The minimax risk cannot exceed the worst-case risk of a feasible sampler. -/
theorem minimax_le_worstCaseRisk [Nonempty ι] (Q R : ℕ)
    (A : BudgetedSampler F Q R) : minimax F Q R ≤ worstCaseRisk F A.1 := by
  exact csInf_le (worstCaseRisk_range_bddBelow F Q R) (Set.mem_range_self A)

/-- With both indexing classes inhabited, minimax TV risk is nonnegative. -/
theorem minimax_nonneg [Nonempty ι] (Q R : ℕ)
    (hne : Nonempty (BudgetedSampler F Q R)) : 0 ≤ minimax F Q R := by
  apply le_minimax_of_forall_worstCaseRisk F Q R 0 hne
  intro A
  exact worstCaseRisk_nonneg F A.1 A.2.2

/-- With both indexing classes inhabited, minimax TV risk is at most one. -/
theorem minimax_le_one [Nonempty ι] (Q R : ℕ)
    (hne : Nonempty (BudgetedSampler F Q R)) : minimax F Q R ≤ 1 := by
  obtain ⟨A⟩ := hne
  exact (minimax_le_worstCaseRisk F Q R A).trans
    (worstCaseRisk_le_one F A.1 A.2.2)


section FinitePrior

variable [Fintype ι]

/-- Averaging instance risks against a finite prior cannot exceed their worst
case.  The normalized prior itself rules out an empty index type. -/
theorem priorRisk_le_worstCaseRisk (π : FinDist ι) (A : RandomizedSamplerData N V)
    (hmeas : ∀ i, A.RiskMeasurableAt (F i)) :
    (∑ i, π i * A.risk (F i)) ≤ worstCaseRisk F A := by
  calc
    (∑ i, π i * A.risk (F i)) ≤ ∑ i, π i * worstCaseRisk F A := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (risk_le_worstCaseRisk F A hmeas i) (π.nonneg i)
    _ = worstCaseRisk F A := by rw [← Finset.sum_mul, π.sum_mass, one_mul]

/-- A finite prior average commutes with the controller-seed integral.  Only
measurability of the individual TV losses is required. -/
theorem priorRisk_eq_integral (π : FinDist ι) (A : RandomizedSamplerData N V)
    (hmeas : ∀ i, A.RiskMeasurableAt (F i)) :
    letI : MeasurableSpace A.Seed := A.seedMeasurableSpace
    (∑ i, π i * A.risk (F i)) =
      ∫ w, ∑ i, π i * FinDist.tv (F i).model.target
        (A.sampler.outputLaw w (F i).oracle) ∂A.seedMeasure := by
  let : MeasurableSpace A.Seed := A.seedMeasurableSpace
  let : IsProbabilityMeasure A.seedMeasure := A.seedIsProbability
  have hint : ∀ i, Integrable
      (fun w ↦ π i * FinDist.tv (F i).model.target
        (A.sampler.outputLaw w (F i).oracle)) A.seedMeasure := by
    intro i
    exact (A.sampler.integrable_seed_loss A.seedMeasure (F i).model (F i).oracle
      (hmeas i)).const_mul (π i)
  rw [integral_finsetSum Finset.univ (fun i _ ↦ hint i)]
  simp only [integral_const_mul, RandomizedSamplerData.risk, Sampler.seedRisk]

/-- A seedwise finite-prior TV lower bound survives averaging over the
controller seed.  No Hellinger-affinity integrand is introduced. -/
theorem le_priorRisk_of_seedwise (π : FinDist ι) (A : RandomizedSamplerData N V)
    (hmeas : ∀ i, A.RiskMeasurableAt (F i)) (c : ℝ)
    (hlower : ∀ w : A.Seed, c ≤ ∑ i, π i * FinDist.tv (F i).model.target
      (A.sampler.outputLaw w (F i).oracle)) :
    c ≤ ∑ i, π i * A.risk (F i) := by
  let : MeasurableSpace A.Seed := A.seedMeasurableSpace
  let : IsProbabilityMeasure A.seedMeasure := A.seedIsProbability
  have hint : Integrable
      (fun w ↦ ∑ i, π i * FinDist.tv (F i).model.target
        (A.sampler.outputLaw w (F i).oracle)) A.seedMeasure := by
    apply integrable_finsetSum Finset.univ
    intro i _
    exact (A.sampler.integrable_seed_loss A.seedMeasure (F i).model (F i).oracle
      (hmeas i)).const_mul (π i)
  calc
    c = ∫ _ : A.Seed, c ∂A.seedMeasure := by simp
    _ ≤ ∫ w, ∑ i, π i * FinDist.tv (F i).model.target
        (A.sampler.outputLaw w (F i).oracle) ∂A.seedMeasure :=
      integral_mono (integrable_const c) hint hlower
    _ = ∑ i, π i * A.risk (F i) := (priorRisk_eq_integral F π A hmeas).symm

/-- A fixed finite hard-instance prior giving a TV lower bound for every
controller seed of every feasible sampler implies the same minimax bound.
All needed TV measurability is already stored in `BudgetedSampler`. -/
theorem le_minimax_of_seedwise_prior (π : FinDist ι) (Q R : ℕ) (c : ℝ)
    (hne : Nonempty (BudgetedSampler F Q R))
    (hlower : ∀ A : BudgetedSampler F Q R, ∀ w : A.1.Seed,
      c ≤ ∑ i, π i * FinDist.tv (F i).model.target
        (A.1.sampler.outputLaw w (F i).oracle)) :
    c ≤ minimax F Q R := by
  apply le_minimax_of_forall_worstCaseRisk F Q R c hne
  intro A
  exact (le_priorRisk_of_seedwise F π A.1 A.2.2 c (hlower A)).trans
    (priorRisk_le_worstCaseRisk F π A.1 A.2.2)

/-- Positive round budgets automatically provide the nonemptiness hypothesis
in the finite-prior minimax bridge. -/
theorem le_minimax_of_seedwise_prior_of_one_le_rounds
    (π : FinDist ι) (Q R : ℕ) (hR : 1 ≤ R) (c : ℝ)
    (hlower : ∀ A : BudgetedSampler F Q R, ∀ w : A.1.Seed,
      c ≤ ∑ i, π i * FinDist.tv (F i).model.target
        (A.1.sampler.outputLaw w (F i).oracle)) :
    c ≤ minimax F Q R := by
  exact le_minimax_of_seedwise_prior F π Q R c
    (budgetedSampler_nonempty F Q R hR) hlower

end FinitePrior

end InstanceFamily

end ForestSampling
