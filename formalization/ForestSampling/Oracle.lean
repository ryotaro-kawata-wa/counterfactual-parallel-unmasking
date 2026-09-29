import ForestSampling.ForestModel

set_option autoImplicit false

namespace ForestSampling

universe u

/-- A masked sequence state; `none` is the mask symbol. -/
abbrev MaskedState (N : ℕ) (V : Type u) := Position N → Option V

namespace MaskedState

variable {N : ℕ} {V : Type u} [DecidableEq V]

/-- Masked coordinates of a state. -/
def masked (y : MaskedState N V) : Finset (Position N) :=
  Finset.univ.filter fun i ↦ y i = none

/-- Observed coordinates of a state. -/
def observed (y : MaskedState N V) : Finset (Position N) :=
  Finset.univ.filter fun i ↦ y i ≠ none

@[simp]
theorem mem_masked_iff (y : MaskedState N V) (i : Position N) :
    i ∈ y.masked ↔ y i = none := by
  simp [masked]

@[simp]
theorem mem_observed_iff (y : MaskedState N V) (i : Position N) :
    i ∈ y.observed ↔ ∃ a, y i = some a := by
  simp only [observed, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    cases hval : y i with
    | none => exact False.elim (hi hval)
    | some a => exact ⟨a, rfl⟩
  · rintro ⟨a, hval⟩ hnone
    rw [hval] at hnone
    exact Option.some_ne_none a hnone

theorem mem_observed_iff_ne_none (y : MaskedState N V) (i : Position N) :
    i ∈ y.observed ↔ y i ≠ none := by
  simp [observed]

theorem masked_disjoint_observed (y : MaskedState N V) :
    Disjoint y.masked y.observed := by
  rw [Finset.disjoint_left]
  intro i him hio
  rw [mem_masked_iff] at him
  rw [mem_observed_iff_ne_none] at hio
  exact hio him

theorem masked_union_observed (y : MaskedState N V) :
    y.masked ∪ y.observed = Finset.univ := by
  ext i
  cases hval : y i with
  | none => simp [hval]
  | some a => simp [mem_observed_iff, hval]

/-- A complete configuration agrees with all observations in `y`. -/
def Agrees (y : MaskedState N V) (x : Configuration N V) : Prop :=
  ∀ i a, y i = some a → x i = a

noncomputable instance (y : MaskedState N V) (x : Configuration N V) :
    Decidable (y.Agrees x) :=
  Classical.propDecidable _

/-- Complete all masks with one common fallback value. -/
def completion (y : MaskedState N V) (fallback : V) : Configuration N V :=
  fun i ↦ (y i).getD fallback

theorem completion_agrees (y : MaskedState N V) (fallback : V) :
    y.Agrees (y.completion fallback) := by
  intro i a hia
  simp [completion, hia]

theorem completion_at_mask (y : MaskedState N V) {j : Position N}
    (hj : y j = none) (fallback : V) :
    y.completion fallback j = fallback := by
  simp [completion, hj]

theorem agrees_nonempty (y : MaskedState N V) [Nonempty V] :
    ∃ x, y.Agrees x := by
  let fallback : V := Classical.choice (inferInstance : Nonempty V)
  exact ⟨y.completion fallback, y.completion_agrees fallback⟩

end MaskedState

/-- A position equipped with evidence that it is masked in `y`. -/
abbrev MaskedPosition {N : ℕ} {V : Type u} [DecidableEq V]
    (y : MaskedState N V) :=
  {i : Position N // i ∈ y.masked}

namespace MaskedState

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- Probability of all observations in a masked state. -/
noncomputable def probability (p : FinDist (Configuration N V))
    (y : MaskedState N V) : ℝ :=
  p.eventMass y.Agrees

theorem probability_pos (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) (y : MaskedState N V) [Nonempty V] :
    0 < y.probability p := by
  exact p.eventMass_pos_of_exists hp y.Agrees y.agrees_nonempty

/-- Exact singleton conditional for a masked readout. -/
noncomputable def exactRow (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) (y : MaskedState N V) [Nonempty V]
    (j : MaskedPosition y) : FinDist V :=
  p.conditionalMap y.Agrees (y.probability_pos p hp) (fun x ↦ x j.1)

theorem exactRow_strictlyPositive (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) (y : MaskedState N V) [Nonempty V]
    (j : MaskedPosition y) :
    (y.exactRow p hp j).StrictlyPositive := by
  apply p.conditionalMap_strictlyPositive hp y.Agrees
    (y.probability_pos p hp) (fun x ↦ x j.1)
  intro a
  refine ⟨y.completion a, y.completion_agrees a, ?_⟩
  exact y.completion_at_mask ((mem_masked_iff y j.1).mp j.2) a

/-- The state with every coordinate masked. -/
def allMask (N : ℕ) (V : Type u) : MaskedState N V :=
  fun _ ↦ none

@[simp]
theorem allMask_apply (i : Position N) : allMask N V i = none := rfl

@[simp]
theorem masked_allMask : (allMask N V).masked = Finset.univ := by
  ext i
  simp

/-- A submitted state respects a committed history if it retains every commit. -/
def RespectsHistory (y : MaskedState N V) (h : History N V) : Prop :=
  ∀ i : h.committed, y i.1 = some (h.value i)

noncomputable instance (y : MaskedState N V) (h : History N V) :
    Decidable (y.RespectsHistory h) :=
  Classical.propDecidable _

/-- The mandatory state immediately before a commit: history visible, residual masked. -/
def commitState (h : History N V) : MaskedState N V :=
  fun i ↦ if hi : i ∈ h.committed then some (h.value ⟨i, hi⟩) else none

theorem commitState_respects (h : History N V) :
    (commitState h).RespectsHistory h := by
  intro i
  simp [commitState]

@[simp]
theorem commitState_masked_iff (h : History N V) (i : Position N) :
    i ∈ (commitState h).masked ↔ i ∉ h.committed := by
  rw [mem_masked_iff]
  by_cases hi : i ∈ h.committed
  · simp [commitState, hi]
  · simp [commitState, hi]

theorem masked_commitState (h : History N V) :
    (commitState h).masked = h.uncommitted := by
  ext i
  rw [commitState_masked_iff, History.mem_uncommitted_iff]

end MaskedState

/-- A deterministic frozen conditional oracle. -/
structure FrozenOracle (N : ℕ) (V : Type u) [Fintype V] [DecidableEq V] where
  row : (y : MaskedState N V) → MaskedPosition y → FinDist V
  row_positive : ∀ y j, (row y j).StrictlyPositive

namespace FrozenOracle

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- All conditional rows returned by one masked-state evaluation.

The whole function is the response to one state submission; asking for many
masked positions therefore does not create additional state submissions.
-/
def readState (O : FrozenOracle N V) (y : MaskedState N V) :
    MaskedPosition y → FinDist V :=
  O.row y

/-- The exact deterministic conditional oracle. -/
noncomputable def exact [Nonempty V] (M : ForestModel N V) : FrozenOracle N V where
  row y j := y.exactRow M.target M.target_positive j
  row_positive y j := y.exactRow_strictlyPositive M.target M.target_positive j

/-- Frozen-oracle accuracy (A2), including the paper's radius domain. -/
def Accurate [Nonempty V] (M : ForestModel N V) (O : FrozenOracle N V)
    (oracleRadius : ℝ) : Prop :=
  0 ≤ oracleRadius ∧ oracleRadius ≤ 1 ∧
    ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.sqHellinger
        (y.exactRow M.target M.target_positive j) (O.row y j) ≤
        oracleRadius ^ 2 / (2 * (N : ℝ))

theorem Accurate.h2_bound [Nonempty V] {M : ForestModel N V}
    {O : FrozenOracle N V} {oracleRadius : ℝ}
    (h : O.Accurate M oracleRadius) (y : MaskedState N V)
    (j : MaskedPosition y) :
    FinDist.sqHellinger
      (y.exactRow M.target M.target_positive j) (O.row y j) ≤
      oracleRadius ^ 2 / (2 * (N : ℝ)) :=
  h.2.2 y j

theorem Accurate.tv_bound [Nonempty V] {M : ForestModel N V}
    {O : FrozenOracle N V} {oracleRadius : ℝ}
    (hN : 0 < N) (h : O.Accurate M oracleRadius)
    (y : MaskedState N V) (j : MaskedPosition y) :
    FinDist.tv
      (y.exactRow M.target M.target_positive j) (O.row y j) ≤
      oracleRadius / Real.sqrt (N : ℝ) := by
  let p := y.exactRow M.target M.target_positive j
  let q := O.row y j
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hH := h.h2_bound y j
  have hscale :
      2 * (oracleRadius ^ 2 / (2 * (N : ℝ))) =
        oracleRadius ^ 2 / (N : ℝ) := by
    field_simp
  have htwo :
      2 * FinDist.sqHellinger p q ≤ oracleRadius ^ 2 / (N : ℝ) := by
    rw [← hscale]
    exact mul_le_mul_of_nonneg_left hH (by norm_num)
  calc
    FinDist.tv p q
        ≤ Real.sqrt (2 * FinDist.sqHellinger p q) :=
          FinDist.tv_le_sqrt_two_mul_sqHellinger p q
    _ ≤ Real.sqrt (oracleRadius ^ 2 / (N : ℝ)) :=
          Real.sqrt_le_sqrt htwo
    _ = oracleRadius / Real.sqrt (N : ℝ) := by
          rw [Real.sqrt_div (sq_nonneg oracleRadius),
            Real.sqrt_sq h.1]

theorem exact_accurate [Nonempty V] (M : ForestModel N V)
    {oracleRadius : ℝ} (hN : 0 < N)
    (hradius0 : 0 ≤ oracleRadius) (hradius1 : oracleRadius ≤ 1) :
    (exact M).Accurate M oracleRadius := by
  refine ⟨hradius0, hradius1, ?_⟩
  intro y j
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  change FinDist.sqHellinger
      (y.exactRow M.target M.target_positive j)
      (y.exactRow M.target M.target_positive j) ≤
    oracleRadius ^ 2 / (2 * (N : ℝ))
  rw [FinDist.sqHellinger_self]
  exact div_nonneg (sq_nonneg oracleRadius)
    (mul_nonneg (by norm_num) hNreal.le)

/-- The class of all deterministic frozen maps satisfying (A2). -/
def Class [Nonempty V] (M : ForestModel N V) (oracleRadius : ℝ) :=
  {O : FrozenOracle N V // O.Accurate M oracleRadius}

end FrozenOracle

end ForestSampling
