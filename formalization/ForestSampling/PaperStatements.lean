import ForestSampling.Algorithm

set_option autoImplicit false

open MeasureTheory

namespace ForestSampling

universe u

/-!
# Legacy finite contracts and shared minimax interfaces

This file retains earlier finite upper and lower contracts as propositions
over the typed model/oracle/algorithm interface. These contracts are not the
current randomized-upper/nonlinear-lower manuscript claims; current lower
parameters and the scalar corollary are in `CurrentStatements`.  They are deliberately *not* declared
as axioms or as proved theorems.  Supporting algebraic consequences that do
not require the paper's combinatorial arguments are proved below.
-/

/-- One target together with the single frozen oracle selected after it. -/
structure SamplingInstance (N : ℕ) (V : Type u)
    [Fintype V] [DecidableEq V] where
  model : ForestModel N V
  oracle : FrozenOracle N V

/-- A sampler together with an arbitrary probability space for its controller seed. -/
structure RandomizedSamplerData (N : ℕ) (V : Type u)
    [Fintype V] [DecidableEq V] where
  Seed : Type u
  seedMeasurableSpace : MeasurableSpace Seed
  seedMeasure : Measure Seed
  seedIsProbability : IsProbabilityMeasure seedMeasure
  sampler : Sampler N V Seed

namespace RandomizedSamplerData

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- Conditional-output TV risk averaged over the stored seed probability law. -/
noncomputable def risk (A : RandomizedSamplerData N V)
    (I : SamplingInstance N V) : ℝ := by
  letI : MeasurableSpace A.Seed := A.seedMeasurableSpace
  exact A.sampler.seedRisk A.seedMeasure I.model I.oracle

/-- The two pathwise resources are bounded uniformly over seeds and replies. -/
def WithinBudgets (A : RandomizedSamplerData N V) (Q R : ℕ) : Prop :=
  A.sampler.WithinBudgets Q R

/-- Measurability of the seedwise risk for one instance. -/
def RiskMeasurableAt (A : RandomizedSamplerData N V)
    (I : SamplingInstance N V) : Prop := by
  letI : MeasurableSpace A.Seed := A.seedMeasurableSpace
  exact AEStronglyMeasurable
    (fun w ↦ FinDist.tv I.model.target (A.sampler.outputLaw w I.oracle))
    A.seedMeasure

end RandomizedSamplerData

namespace InstanceFamily

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- Worst-case risk over a typed instance family. -/
noncomputable def worstCaseRisk {ι : Type u}
    (F : ι → SamplingInstance N V) (A : RandomizedSamplerData N V) : ℝ :=
  sSup (Set.range fun i ↦ A.risk (F i))

/-- A budgeted sampler whose seedwise risk is measurable on the whole family. -/
def BudgetedSampler {ι : Type u} (F : ι → SamplingInstance N V)
    (Q R : ℕ) :=
  {A : RandomizedSamplerData N V //
    A.WithinBudgets Q R ∧ ∀ i, A.RiskMeasurableAt (F i)}

/-- Minimax risk under simultaneous pathwise query and commit-round budgets. -/
noncomputable def minimax {ι : Type u}
    (F : ι → SamplingInstance N V) (Q R : ℕ) : ℝ :=
  sInf (Set.range fun A : BudgetedSampler F Q R ↦
    worstCaseRisk F A.1)

end InstanceFamily

/-- Scalar hypotheses of the finite hard-matching construction. -/
structure MatchingLowerParameters (N : ℕ) where
  vocabSize : ℕ
  bankSize : ℕ
  triggerMass : ℝ
  edgeCoupling : ℝ
  even_length : Even N
  bank_nonempty : 1 ≤ bankSize
  bank_lt_vocab : bankSize < vocabSize
  bank_mass_lt_one : (bankSize : ℝ) * triggerMass < 1
  coupling_pos : 0 < edgeCoupling
  coupling_le_trigger : edgeCoupling ≤ triggerMass
  trigger_le_half : triggerMass ≤ (1 / 2 : ℝ)
  finite_separation : (N : ℝ) * edgeCoupling ^ 2 ≤ 1

namespace MatchingLowerParameters

variable {N : ℕ}

/-- The numerical lower-bound value in Theorem `app:thm:finite-lower`. -/
noncomputable def lowerValue (P : MatchingLowerParameters N) (R : ℕ) : ℝ :=
  (N : ℝ) * P.edgeCoupling ^ 2 / (768 * (R : ℝ))

end MatchingLowerParameters

/-- Typed form of the finite adaptive query--round lower-bound statement.

The argument `hardFamily` is to be instantiated by the explicit matching
construction.  Its target, oracle, algorithm interface, conditional-output
risk, and the order of the infimum/supremum are no longer informal here.
-/
def FiniteAdaptiveLowerBound {N : ℕ} {V : Type u}
    [Fintype V] [DecidableEq V] {ι : Type u}
    (P : MatchingLowerParameters N)
    (hardFamily : ι → SamplingInstance N V) : Prop :=
  Fintype.card V = P.vocabSize ∧
    ∀ (Q R : ℕ),
      Q ≤ P.bankSize / 8 → 1 ≤ R → R ≤ N / 8 →
      P.lowerValue R ≤ InstanceFamily.minimax hardFamily Q R

/-- Purely algebraic target-error consequence of a finite lower estimate.

This proves the logical step used in `app:cor:finite-target-tradeoff`; the
combinatorial lower estimate itself remains the substantive theorem.
-/
theorem finite_target_error_alternative {N : ℕ}
    (P : MatchingLowerParameters N) (Q R : ℕ) (risk ε : ℝ)
    (hε : 0 < ε) (hR : 1 ≤ R) (hrisk : risk ≤ ε)
    (hlower : Q ≤ P.bankSize / 8 → R ≤ N / 8 →
      P.lowerValue R ≤ risk) :
    P.bankSize / 8 < Q ∨ N / 8 < R ∨
      (N : ℝ) * P.edgeCoupling ^ 2 / (768 * ε) ≤ (R : ℝ) := by
  by_cases hQ : Q ≤ P.bankSize / 8
  · by_cases hRN : R ≤ N / 8
    · right
      right
      have hRreal : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR)
      have hdenR : 0 < (768 : ℝ) * (R : ℝ) := mul_pos (by norm_num) hRreal
      have hbase : P.lowerValue R ≤ ε := (hlower hQ hRN).trans hrisk
      have hnum :
          (N : ℝ) * P.edgeCoupling ^ 2 ≤ ε * (768 * (R : ℝ)) := by
        exact (div_le_iff₀ hdenR).mp hbase
      have hdenE : 0 < (768 : ℝ) * ε := mul_pos (by norm_num) hε
      apply (div_le_iff₀ hdenE).2
      nlinarith
    · exact Or.inr (Or.inl (Nat.lt_of_not_ge hRN))
  · exact Or.inl (Nat.lt_of_not_ge hQ)

/-- Finite parameters appearing explicitly in the upper resource bounds. -/
structure FiniteUpperParameters (N : ℕ) where
  maxBankSize : ℕ
  peelPhaseCap : ℕ
  colorPrime : ℕ
  chunkCount : ℕ
  degreeCutoff : ℕ
  screenResolution : ℝ
  edgeSignal : ℝ
  length_at_least_ten : 10 ≤ N
  degreeCutoff_pos : 0 < degreeCutoff

namespace FiniteUpperParameters

variable {N : ℕ}

/-- Right-hand side of `app:eq:finite-upper-Q` (without all-mask charge). -/
def queryBound (P : FiniteUpperParameters N) : ℕ :=
  P.maxBankSize * (P.peelPhaseCap + 1) *
    P.colorPrime ^ 2 * (P.colorPrime + P.chunkCount)

/-- Right-hand side of the strict commit-round inequality. -/
noncomputable def roundBound (P : FiniteUpperParameters N) : ℝ :=
  (8 * (N : ℝ) * P.peelPhaseCap) / P.degreeCutoff +
    (Nat.clog 2 (N + 1) : ℝ)

end FiniteUpperParameters

/-- Typed form of the finite exact-certification upper-bound statement. -/
def FiniteExactCertificationUpperBound {N : ℕ} {V : Type u}
    [Fintype V] [DecidableEq V] [Nonempty V]
    {Seed : Type u} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (P : FiniteUpperParameters N) (preprocessingFeasible : Prop)
    (M : ForestModel N V) (oracleRadius : ℝ)
    (packedSampler : Sampler N V Seed) : Prop :=
  preprocessingFeasible → P.screenResolution < P.edgeSignal →
    packedSampler.RiskMeasurable μ M oracleRadius ∧
    (∃ Q R : ℕ,
      packedSampler.WithinBudgets Q R ∧
      Q ≤ P.queryBound ∧ (R : ℝ) < P.roundBound) ∧
    (∀ O : FrozenOracle N V, O.Accurate M oracleRadius →
      packedSampler.seedRisk μ M O ≤ oracleRadius) ∧
    packedSampler.robustRisk μ M oracleRadius ≤ oracleRadius

/-- A positionwise ranking of tokens by nonincreasing exact marginal mass. -/
structure MarginalRanking {N : ℕ} {V : Type u}
    [Fintype V] [DecidableEq V] (M : ForestModel N V) where
  token : Position N → Fin (Fintype.card V) → V
  token_bijective : ∀ i, Function.Bijective (token i)
  nonincreasing : ∀ i k l, k ≤ l →
    M.marginal i (token i l) ≤ M.marginal i (token i k)

/-- The finite rank--frequency inequality used in the family-inclusion claim. -/
def FiniteRankFrequency {N : ℕ} {V : Type u}
    [Fintype V] [DecidableEq V] (M : ForestModel N V)
    (ranking : MarginalRanking M) (exponent constant : ℝ) : Prop :=
  ∀ (i : Position N) (k : Fin (Fintype.card V)),
    M.marginal i (ranking.token i k) ≤
      constant * (((k.1 + 1 : ℕ) : ℝ) ^ (-exponent) +
        1 / (Fintype.card V : ℝ))

/-- Typed conclusion of the finite hard-family inclusion proposition. -/
def FiniteHardFamilyIncluded {N : ℕ} {V : Type u}
    [Fintype V] [DecidableEq V] [Nonempty V] {ι : Type u}
    (hardFamily : ι → SamplingInstance N V)
    (rankings : ∀ i, MarginalRanking (hardFamily i).model)
    (rankExponent edgeSignal oracleRadius : ℝ) : Prop :=
  1 < rankExponent ∧
    ∀ i,
      (hardFamily i).model.TailResponseRegular 1 1 ∧
      (hardFamily i).model.EdgeNondegenerate edgeSignal ∧
      FiniteRankFrequency (hardFamily i).model (rankings i) rankExponent 1 ∧
      (hardFamily i).oracle.Accurate (hardFamily i).model oracleRadius

end ForestSampling
