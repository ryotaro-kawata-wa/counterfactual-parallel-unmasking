import ForestSampling.ThresholdGrid
import ForestSampling.PackedParameters

set_option autoImplicit false

namespace ForestSampling
namespace ThresholdGrid

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The exact public preprocessing floor used before every oracle call. -/
noncomputable def standardFloor (N : ℕ) (V : Type*) [Fintype V] (ρ F : ℝ) : ℝ :=
  4 * max (ρ / Real.sqrt N) (F / (Fintype.card V : ℝ))

theorem standardFloor_pos (ρ F : ℝ) (hF : 1 ≤ F) : 0 < standardFloor N V ρ F := by
  have hv : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hFp : 0 < F := by linarith
  have hp : 0 < 4 * (F / (Fintype.card V : ℝ)) := by positivity
  exact hp.trans_le (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))

/-- All certificates of the actual maximum feasible grid threshold. The
bank complement follows from the public floor, with no oracle inspection. -/
theorem standard_selected_spec (ρ F C s ν : ℝ) (hF : 1 ≤ F)
    (hf1 : standardFloor N V ρ F ≤ 1)
    (hgrid : (feasible (standardFloor N V ρ F) C s ν).Nonempty) :
    let t := selected (standardFloor N V ρ F) C s ν hgrid
    0 < t ∧ t ≤ 1 ∧ min 1 (C * t ^ s) ≤ ν ∧
      (Fintype.card V : ℝ)⁻¹ < t - ρ / Real.sqrt N ∧
      standardFloor N V ρ F ≤ t := by
  intro t
  have hf := standardFloor_pos (N := N) (V := V) ρ F hF
  have hs := selected_spec (standardFloor N V ρ F) C s ν hf hf1 hgrid
  exact ⟨hf.trans_le hs.1, hs.2.1, hs.2.2,
    Screening.standardFloor_complement_bound _ F t hF hs.1, hs.1⟩

/-- The actual selected threshold produces the concrete sampler's complete
public parameter object, including all phase, color, chunk, and round caps. -/
noncomputable def parameters (N : ℕ) (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V]
    (D L : ℕ) (ρ η F C s ν : ℝ) (hN : 0 < N) (hL : 0 < L)
    (hF : 1 ≤ F) (hf1 : standardFloor N V ρ F ≤ 1)
    (hgrid : (feasible (standardFloor N V ρ F) C s ν).Nonempty) :
    PackedSampler.Parameters N V :=
  PackedSampler.manuscriptParameters N V D L
    (selected (standardFloor N V ρ F) C s ν hgrid) ρ η hN hL
    (standard_selected_spec ρ F C s ν hF hf1 hgrid).2.2.2.1

/-- Finite RF bounds apply directly to banks built by this public grid
choice and the oracle's actual all-mask observations. -/
theorem selected_bankMax_le [LinearOrder V] (M : ForestModel N V) (O : FrozenOracle N V)
    (ranking : MarginalRanking M) (ρ F exponent C s ν : ℝ)
    (hF : 1 ≤ F) (he : 0 < exponent)
    (hf1 : standardFloor N V ρ F ≤ 1)
    (hgrid : (feasible (standardFloor N V ρ F) C s ν).Nonempty)
    (hRF : FiniteRankFrequency M ranking exponent F)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.tv (y.exactRow M.target M.target_positive j) (O.row y j) ≤ ρ / Real.sqrt N) :
    let t := selected (standardFloor N V ρ F) C s ν hgrid
    let hfloor := (standard_selected_spec ρ F C s ν hF hf1 hgrid).2.2.2.1
    (Screening.Banks.ofOracle O t (ρ / Real.sqrt N) hfloor).maxSize ≤
      ⌊(4 * F / t) ^ (1 / exponent)⌋₊ := by
  exact Screening.bankMax_le_rank_bound M O ranking exponent F _ _ he hF hRF
    (standard_selected_spec ρ F C s ν hF hf1 hgrid).2.2.2.2 hrows

end ThresholdGrid
end ForestSampling
