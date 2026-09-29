import ForestSampling.Screening

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace Screening

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Strict majority is correct when a strict majority of trials agrees
with a truth value. Ties are rejected by the actual vote rule. -/
theorem majority_iff_of_good_majority (good vote : ι → Prop)
    [DecidablePred good] [DecidablePred vote] (truth : Prop)
    (hgood : Fintype.card ι < 2 * (Finset.univ.filter good).card)
    (hcorrect : ∀ τ, good τ → (vote τ ↔ truth)) :
    (Fintype.card ι < 2 * (Finset.univ.filter vote).card) ↔ truth := by
  constructor
  · intro hvote
    by_contra hfalse
    have hdisjoint : Disjoint (Finset.univ.filter good) (Finset.univ.filter vote) := by
      apply Finset.disjoint_left.mpr
      intro τ hg hv
      exact hfalse ((hcorrect τ (Finset.mem_filter.mp hg).2).mp (Finset.mem_filter.mp hv).2)
    have hcap := Finset.card_le_card
      (Finset.subset_univ ((Finset.univ.filter good) ∪ (Finset.univ.filter vote)))
    rw [Finset.card_union_of_disjoint hdisjoint, Finset.card_univ] at hcap
    omega
  · intro htruth
    have hsub : Finset.univ.filter good ⊆ Finset.univ.filter vote := by
      intro τ hτ
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (hcorrect τ (Finset.mem_filter.mp hτ).2).mpr htruth⟩
    have := Finset.card_le_card hsub
    omega

variable {N : ℕ} {V Color : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable [DecidableEq Color]

/-- The actual residual neighbor set, used only in the proof. -/
noncomputable def residualNeighbors (M : ForestModel N V) (h : History N V)
    (j : ResidualVertex h) : Finset (ResidualVertex h) := by
  classical
  exact Finset.univ.filter (fun i ↦ M.graph.Adj i.val j.val)

/-- A color block succeeds if every ordered pair whose readout has degree
at most the cutoff has a strict separating majority. This event contains
no bank-value or draft union. -/
noncomputable def ScreenSuccess (M : ForestModel N V) (h : History N V)
    (colors : ι → Position N → Color) (cutoff : ℕ) : Prop := by
  classical
  exact ∀ i j : ResidualVertex h, i ≠ j → (residualNeighbors M h j).card ≤ cutoff →
    Fintype.card ι < 2 * (Finset.univ.filter (fun τ ↦ Separating M h (colors τ) i j)).card

/-- The candidate set uses only actual observable votes and public inputs. -/
noncomputable def candidateRow [LinearOrder V] (O : FrozenOracle N V)
    (h : History N V) (B : Banks (N := N) (V := V)) (draft : Position N → V)
    (colors : ι → Position N → Color) (chunkSize : ℕ) (ε : ℝ)
    (j : ResidualVertex h) : Finset (ResidualVertex h) := by
  classical
  exact Finset.univ.filter (fun i ↦ i ≠ j ∧
    Fintype.card ι < 2 * (Finset.univ.filter (fun τ ↦ Vote O h B draft (colors τ) chunkSize ε i j)).card)

/-- Successful strict majorities recover the actual entire low-degree
neighbor set from the concrete banks, probes, noisy replies, and votes. -/
theorem candidateRow_eq_neighbors [LinearOrder V] (M : ForestModel N V)
    (O : FrozenOracle N V) (h : History N V) (draft : Position N → V)
    (colors : ι → Position N → Color) (chunkSize cutoff : ℕ)
    (C s t ε ν signal : ℝ)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ε)
    (hε : 0 ≤ ε) (hν : 0 ≤ ν) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hRT : M.TailResponseRegular C s) (hUEN : M.EdgeNondegenerate signal)
    (hfeasible : min 1 (C * t ^ s) ≤ ν) (hmargin : 4 * ε + ν < signal)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.tv (y.exactRow M.target M.target_positive j) (O.row y j) ≤ ε)
    (hsuccess : ScreenSuccess M h colors cutoff) (j : ResidualVertex h)
    (hdegree : (residualNeighbors M h j).card ≤ cutoff) :
    candidateRow O h (Banks.ofOracle O t ε hfloor) draft colors chunkSize ε j =
      residualNeighbors M h j := by
  classical
  ext i
  simp only [candidateRow, residualNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hij : i = j
  · subst i
    simp
  · simp only [ne_eq, hij, not_false_eq_true, true_and]
    apply majority_iff_of_good_majority
      (fun τ ↦ Separating M h (colors τ) i j) _ _ (hsuccess i j hij hdegree)
    intro τ hsep
    constructor
    · intro hvote
      by_contra hnonedge
      exact not_vote_of_separating_nonedge M O h (Banks.ofOracle O t ε hfloor)
        draft (colors τ) chunkSize ε hrows i j (Subtype.coe_injective.ne hij) hsep hnonedge hvote
    · intro hedge
      exact vote_of_separating_edge M O h draft (colors τ) chunkSize C s t ε ν signal
        hfloor hε hν ht0 ht1 hRT hUEN hfeasible hmargin hrows i j hsep hedge

end Screening

/-- A public selector has a hard cap and keeps the full candidate row on
nonoverflow. Its input type excludes target graphs and unobserved randomness. -/
structure PublicRowSelector (α Transcript : Type*) [Fintype α] [DecidableEq α] where
  choose : α → Finset α → ℕ → Transcript → Finset α
  subset : ∀ j C cutoff transcript, choose j C cutoff transcript ⊆ C
  card_le : ∀ j C cutoff transcript, (choose j C cutoff transcript).card ≤ cutoff
  preserves : ∀ j C cutoff transcript, C.card ≤ cutoff → choose j C cutoff transcript = C

namespace PublicRowSelector

variable {α Transcript : Type*} [Fintype α] [DecidableEq α]

/-- The manuscript's admissible alternative that returns no candidates on
overflow. This provides a concrete public selector with both required laws. -/
def dropOverflow : PublicRowSelector α Transcript where
  choose := fun _ C cutoff _ ↦ if C.card ≤ cutoff then C else ∅
  subset := by intro j C cutoff transcript; split <;> simp
  card_le := by intro j C cutoff transcript; split <;> simp_all
  preserves := by intro j C cutoff transcript h; simp [h]

end PublicRowSelector

namespace Screening

variable {N : ℕ} {V Color ι Transcript : Type*}
variable [Fintype V] [DecidableEq V] [Nonempty V] [LinearOrder V]
variable [Fintype ι] [DecidableEq ι] [DecidableEq Color]

/-- The screen returns early with empty rows when all banks are empty;
otherwise the chosen public selector caps the actual strict-majority row. -/
noncomputable def returnedRow (O : FrozenOracle N V) (h : History N V)
    (B : Banks (N := N) (V := V)) (draft : Position N → V)
    (colors : ι → Position N → Color) (chunkSize cutoff : ℕ) (ε : ℝ)
    (selector : PublicRowSelector (ResidualVertex h) Transcript) (transcript : Transcript)
    (j : ResidualVertex h) : Finset (ResidualVertex h) :=
  if B.maxSize = 0 then ∅
  else selector.choose j (candidateRow O h B draft colors chunkSize ε j) cutoff transcript

omit [Nonempty V] [DecidableEq ι] in
/-- The public row cap holds on every execution, including unsuccessful
screens and arbitrary high-degree vertices. -/
theorem returnedRow_card_le (O : FrozenOracle N V) (h : History N V)
    (B : Banks (N := N) (V := V)) (draft : Position N → V)
    (colors : ι → Position N → Color) (chunkSize cutoff : ℕ) (ε : ℝ)
    (selector : PublicRowSelector (ResidualVertex h) Transcript) (transcript : Transcript)
    (j : ResidualVertex h) :
    (returnedRow O h B draft colors chunkSize cutoff ε selector transcript j).card ≤ cutoff := by
  unfold returnedRow
  split
  · simp
  · exact selector.card_le _ _ _ _

/-- The complete deterministic low-degree screen contract for every
admissible public selector, including the all-empty-bank early exit. -/
theorem returnedRow_eq_neighbors (M : ForestModel N V) (O : FrozenOracle N V)
    (h : History N V) (draft : Position N → V)
    (colors : ι → Position N → Color) (chunkSize cutoff : ℕ)
    (C s t ε ν signal : ℝ)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ε)
    (hε : 0 ≤ ε) (hν : 0 ≤ ν) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hRT : M.TailResponseRegular C s) (hUEN : M.EdgeNondegenerate signal)
    (hfeasible : min 1 (C * t ^ s) ≤ ν) (hmargin : 4 * ε + ν < signal)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.tv (y.exactRow M.target M.target_positive j) (O.row y j) ≤ ε)
    (hsuccess : ScreenSuccess M h colors cutoff)
    (selector : PublicRowSelector (ResidualVertex h) Transcript) (transcript : Transcript)
    (j : ResidualVertex h) (hdegree : (residualNeighbors M h j).card ≤ cutoff) :
    returnedRow O h (Banks.ofOracle O t ε hfloor) draft colors chunkSize cutoff ε
      selector transcript j = residualNeighbors M h j := by
  classical
  let B := Banks.ofOracle O t ε hfloor
  change (if B.maxSize = 0 then ∅ else _) = _
  split
  · rename_i hzero
    symm
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hedge : M.graph.Adj i.val j.val := (Finset.mem_filter.mp hi).2
    have hcard := B.card_le_maxSize i
    have hempty : tokenBank O t ε i = ∅ := by
      apply Finset.card_eq_zero.mp
      change (B.bank i).card = 0
      omega
    exact not_adj_of_empty_bank M O C s t ε ν signal hRT ht0 ht1 hfeasible hrows hUEN
      (by linarith) hedge.ne (fixedBoundary h draft i j) hempty hedge
  · rw [candidateRow_eq_neighbors M O h draft colors chunkSize cutoff C s t ε ν signal
      hfloor hε hν ht0 ht1 hRT hUEN hfeasible hmargin hrows hsuccess j hdegree]
    exact selector.preserves _ _ _ _ hdegree

end Screening
end ForestSampling
