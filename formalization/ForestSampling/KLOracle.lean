import ForestSampling.FiniteKL
import ForestSampling.Algorithm

set_option autoImplicit false
open MeasureTheory

namespace ForestSampling

universe u v

namespace FrozenOracle

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Uniform forward-KL row accuracy in `app:def:kl-oracle-risk`.
The exact conditional is the first KL argument; reversing it would specify a
different oracle class. This condition ranges over every masked state. -/
def ForwardKLAccurate (M : ForestModel N V) (O : FrozenOracle N V)
    (rowBudget : ℝ) : Prop :=
  0 ≤ rowBudget ∧ ∀ (y : MaskedState N V) (j : MaskedPosition y),
    FinDist.klDivergence (y.exactRow M.target M.target_positive j) (O.row y j) ≤ rowBudget

/-- Read the row bound without changing the direction of KL. -/
theorem ForwardKLAccurate.row_bound {M : ForestModel N V} {O : FrozenOracle N V}
    {rowBudget : ℝ} (h : O.ForwardKLAccurate M rowBudget)
    (y : MaskedState N V) (j : MaskedPosition y) :
    FinDist.klDivergence (y.exactRow M.target M.target_positive j) (O.row y j) ≤ rowBudget :=
  h.2 y j

/-- The exact oracle belongs to every nonnegative forward-KL row class. -/
theorem exact_forwardKLAccurate (M : ForestModel N V) {rowBudget : ℝ}
    (hbudget : 0 ≤ rowBudget) : (exact M).ForwardKLAccurate M rowBudget := by
  refine ⟨hbudget, ?_⟩
  intro y j
  change FinDist.klDivergence (y.exactRow M.target M.target_positive j)
    (y.exactRow M.target M.target_positive j) ≤ rowBudget
  simpa using hbudget

/-- The calibrated forward-KL class is included in the Hellinger row class,
with the manuscript's normalization and the same public radius. -/
theorem ForwardKLAccurate.accurate {M : ForestModel N V} {O : FrozenOracle N V}
    {rowBudget oracleRadius : ℝ} (h : O.ForwardKLAccurate M rowBudget)
    (hradius0 : 0 ≤ oracleRadius) (hradius1 : oracleRadius ≤ 1)
    (hscale : rowBudget ≤ oracleRadius ^ 2 / (N : ℝ)) :
    O.Accurate M oracleRadius := by
  refine ⟨hradius0, hradius1, ?_⟩
  intro y j
  calc
    FinDist.sqHellinger (y.exactRow M.target M.target_positive j) (O.row y j) ≤
        FinDist.klDivergence (y.exactRow M.target M.target_positive j) (O.row y j) / 2 :=
      FinDist.sqHellinger_le_half_klDivergence _ _
        (y.exactRow_strictlyPositive M.target M.target_positive j) (O.row_positive y j)
    _ ≤ rowBudget / 2 := div_le_div_of_nonneg_right (h.row_bound y j) (by norm_num)
    _ ≤ (oracleRadius ^ 2 / (N : ℝ)) / 2 :=
      div_le_div_of_nonneg_right hscale (by norm_num)
    _ = oracleRadius ^ 2 / (2 * (N : ℝ)) := by ring

/-- All frozen maps in the forward-KL case for a fixed target and row budget. -/
def ForwardKLClass (M : ForestModel N V) (rowBudget : ℝ) :=
  {O : FrozenOracle N V // O.ForwardKLAccurate M rowBudget}

end FrozenOracle

namespace Sampler

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]
variable {Seed : Type v} [MeasurableSpace Seed]

/-- Mean fixed-seed forward KL, with the target as the first argument.
This is the paper's seed-averaged loss, not KL to the seed-mixture output. -/
noncomputable def seedKLRisk (A : Sampler N V Seed) (μ : Measure Seed)
    (M : ForestModel N V) (O : FrozenOracle N V) : ℝ :=
  ∫ w, FinDist.klDivergence M.target (A.outputLaw w O) ∂μ

/-- Measurability of the actual fixed-seed KL losses for one target/oracle pair.
Integrability still requires a finite bound and is proved where that bound is
available; this proposition alone does not assert integrability. -/
def KLRiskMeasurableAt (A : Sampler N V Seed) (μ : Measure Seed)
    (M : ForestModel N V) (O : FrozenOracle N V) : Prop :=
  AEStronglyMeasurable (fun w ↦ FinDist.klDivergence M.target (A.outputLaw w O)) μ

end Sampler
end ForestSampling
