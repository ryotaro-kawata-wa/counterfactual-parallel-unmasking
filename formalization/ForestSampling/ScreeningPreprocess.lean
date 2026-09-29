import ForestSampling.ForestConditionals
import ForestSampling.FiniteCoupling

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace FinDist

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A single atom differs by at most total variation, with the paper's
factor-one-half convention. -/
theorem abs_apply_sub_le_tv (p q : FinDist α) (a : α) :
    |p a - q a| ≤ tv p q := by
  have hzero : (∑ x, (p x - q x)) = 0 := by
    rw [Finset.sum_sub_distrib, p.sum_mass, q.sum_mass, sub_self]
  have hsigned := Finset.sum_erase_add (Finset.univ : Finset α)
    (fun x ↦ p x - q x) (Finset.mem_univ a)
  have habs := Finset.sum_erase_add (Finset.univ : Finset α)
    (fun x ↦ |p x - q x|) (Finset.mem_univ a)
  have hrest : (∑ x ∈ Finset.univ.erase a, (p x - q x)) = -(p a - q a) := by
    linarith
  have htriangle := Finset.abs_sum_le_sum_abs
    (fun x ↦ p x - q x) (Finset.univ.erase a)
  rw [hrest, abs_neg] at htriangle
  unfold tv
  linarith

omit [DecidableEq α] in
/-- Every finite probability row contains an atom no heavier than the
uniform atom. This supplies a certified omitted token in preprocessing. -/
theorem exists_apply_le_inv_card [Nonempty α] (p : FinDist α) :
    ∃ a, p a ≤ (Fintype.card α : ℝ)⁻¹ := by
  by_contra h
  push Not at h
  have hs : (∑ _ : α, (Fintype.card α : ℝ)⁻¹) < ∑ a, p a :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun a _ ↦ h a)
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [p.sum_mass, hc] at hs

end FinDist

namespace Screening

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The all-mask row is obtained from the one public preprocessing reply. -/
noncomputable def noisyMarginal (O : FrozenOracle N V) (i : Position N) : FinDist V :=
  O.row (MaskedState.allMask N V) ⟨i, by simp⟩

/-- The buffered vocabulary bank, defined entirely from the frozen oracle's
public all-mask row and the public threshold and row-TV allowance. -/
noncomputable def tokenBank (O : FrozenOracle N V) (t ε : ℝ) (i : Position N) : Finset V :=
  Finset.univ.filter (fun a ↦ t - ε ≤ noisyMarginal O i a)

omit [Nonempty V] in
theorem mem_tokenBank_iff (O : FrozenOracle N V) (t ε : ℝ) (i : Position N) (a : V) :
    a ∈ tokenBank O t ε i ↔ t - ε ≤ noisyMarginal O i a := by
  simp [tokenBank]

omit [DecidableEq V] in
/-- The floor used by the manuscript is stronger than the atom threshold
needed for a nonempty bank complement. -/
theorem standardFloor_complement_bound (ε C t : ℝ) (hC : 1 ≤ C)
    (ht : 4 * max ε (C / (Fintype.card V : ℝ)) ≤ t) :
    (Fintype.card V : ℝ)⁻¹ < t - ε := by
  have hv : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have hinv : 0 < (Fintype.card V : ℝ)⁻¹ := inv_pos.mpr hv
  have hfreq : (Fintype.card V : ℝ)⁻¹ ≤ C / (Fintype.card V : ℝ) := by
    simpa [one_div] using div_le_div_of_nonneg_right hC hv.le
  have hmax1 := le_max_left ε (C / (Fintype.card V : ℝ))
  have hmax2 := le_max_right ε (C / (Fintype.card V : ℝ))
  linarith

theorem tokenBank_complement_nonempty (O : FrozenOracle N V) (t ε : ℝ)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ε) (i : Position N) :
    (Finset.univ \ tokenBank O t ε i).Nonempty := by
  obtain ⟨a, ha⟩ := (noisyMarginal O i).exists_apply_le_inv_card
  refine ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  rw [mem_tokenBank_iff]
  linarith

theorem exactRow_allMask (M : ForestModel N V) (i : Position N) :
    (MaskedState.allMask N V).exactRow M.target M.target_positive
      ⟨i, by simp⟩ = M.marginal i := by
  unfold MaskedState.exactRow
  have hevent : (MaskedState.allMask N V).Agrees = fun _ ↦ True := by
    funext x
    apply propext
    simp [MaskedState.Agrees, MaskedState.allMask]
  simpa [hevent, ForestModel.marginal, FinDist.positionMarginal] using
    M.target.conditionalMap_true (fun x ↦ x i)

theorem marginal_error_le (M : ForestModel N V) (O : FrozenOracle N V) (ε : ℝ)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.tv (y.exactRow M.target M.target_positive j) (O.row y j) ≤ ε)
    (i : Position N) (a : V) :
    |M.marginal i a - noisyMarginal O i a| ≤ ε := by
  have h := hrows (MaskedState.allMask N V) ⟨i, by simp⟩
  rw [exactRow_allMask] at h
  exact ((M.marginal i).abs_apply_sub_le_tv (noisyMarginal O i) a).trans h

/-- Every omitted token is in the target's actual marginal tail. -/
theorem outside_bank_mem_tail (M : ForestModel N V) (O : FrozenOracle N V)
    (t ε : ℝ)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.tv (y.exactRow M.target M.target_positive j) (O.row y j) ≤ ε)
    (i : Position N) (a : V) (ha : a ∉ tokenBank O t ε i) :
    a ∈ M.tailSet i t := by
  rw [mem_tokenBank_iff, not_le] at ha
  rw [M.mem_tailSet_iff]
  have hm := (abs_le.mp (marginal_error_le M O ε hrows i a)).2
  linarith

/-- The standard noise floor also supplies the lower mass of each bank
member used by the separate rank-envelope size estimate. -/
theorem bank_member_mass_le (M : ForestModel N V) (O : FrozenOracle N V)
    (t ε : ℝ) (ht : 4 * ε ≤ t)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.tv (y.exactRow M.target M.target_positive j) (O.row y j) ≤ ε)
    (i : Position N) (a : V) (ha : a ∈ tokenBank O t ε i) :
    t / 2 ≤ M.marginal i a := by
  rw [mem_tokenBank_iff] at ha
  have hm := (abs_le.mp (marginal_error_le M O ε hrows i a)).1
  linarith

/-- Reusable public preprocessing data. The only stored certificate concerns
the public bank complement; no target graph or response witness is stored. -/
structure Banks where
  bank : Position N → Finset V
  tail : Position N → V
  tail_not_mem : ∀ i, tail i ∉ bank i

namespace Banks

/-- Build the actual bank tuple, choosing its tail token in the public order. -/
noncomputable def ofOracle [LinearOrder V] (O : FrozenOracle N V) (t ε : ℝ)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ε) : Banks (N := N) (V := V) where
  bank := tokenBank O t ε
  tail := fun i ↦ (Finset.univ \ tokenBank O t ε i).min'
    (tokenBank_complement_nonempty O t ε hfloor i)
  tail_not_mem := fun _ ↦ (Finset.mem_sdiff.mp (Finset.min'_mem _ _)).2

/-- The maximum bank length determines the shared packed-column count. -/
def maxSize (B : Banks (N := N) (V := V)) : ℕ := Finset.univ.sup (fun i ↦ (B.bank i).card)

omit [Fintype V] [DecidableEq V] [Nonempty V] in
theorem card_le_maxSize (B : Banks (N := N) (V := V)) (i : Position N) :
    (B.bank i).card ≤ B.maxSize := by
  exact Finset.le_sup (f := fun i ↦ (B.bank i).card) (Finset.mem_univ i)

/-- `none` is the final tail column; `some k` is the zero-based public bank
column, padded by the fixed draft when that local bank is shorter. -/
abbrev Column (B : Banks (N := N) (V := V)) := Option (Fin B.maxSize)

noncomputable def packedColumn [LinearOrder V] (B : Banks (N := N) (V := V))
    (draft : Position N → V) (column : B.Column) (i : Position N) : V :=
  match column with
  | none => B.tail i
  | some k => if hk : k.val < (B.bank i).card then
      (B.bank i).orderEmbOfFin rfl ⟨k.val, hk⟩ else draft i

omit [Fintype V] [DecidableEq V] [Nonempty V] in
@[simp] theorem packedColumn_tail [LinearOrder V] (B : Banks (N := N) (V := V))
    (draft : Position N → V) (i : Position N) :
    B.packedColumn draft none i = B.tail i := rfl

omit [Fintype V] [DecidableEq V] [Nonempty V] in
/-- Every local bank token occurs in one of the shared packed columns. -/
theorem packedColumn_covers_bank [LinearOrder V] (B : Banks (N := N) (V := V))
    (draft : Position N → V) (i : Position N) (a : V) (ha : a ∈ B.bank i) :
    ∃ column : B.Column, B.packedColumn draft column i = a := by
  let k := ((B.bank i).orderIsoOfFin rfl).symm ⟨a, ha⟩
  have hk : k.val < (B.bank i).card := k.isLt
  refine ⟨some ⟨k.val, lt_of_lt_of_le hk (B.card_le_maxSize i)⟩, ?_⟩
  simp only [packedColumn, dif_pos hk]
  exact congrArg Subtype.val (((B.bank i).orderIsoOfFin rfl).apply_symm_apply ⟨a, ha⟩)

end Banks
end Screening
end ForestSampling
