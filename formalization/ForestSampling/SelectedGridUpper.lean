import ForestSampling.GridPreprocessing
import ForestSampling.SelectedPackedUpper

set_option autoImplicit false

namespace ForestSampling
namespace SelectedThresholdGrid

open ThresholdGrid

variable {N : ℕ} {V State : Type*}
variable [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]

/-- The original public dyadic preprocessing choice satisfies the concrete
TV theorem. Feasibility refers to the actual finite grid, not a surrogate
continuous threshold or an oracle-dependent existential choice. -/
theorem grid_seedRisk_le (M : ForestModel N V) (O : FrozenOracle N V)
    (D L : ℕ) (ρ η F C s ν signal : ℝ)
    (hN : 0 < N) (hD : 9 ≤ D) (hL : 0 < L) (hF : 1 ≤ F)
    (hf1 : standardFloor N V ρ F ≤ 1)
    (hgrid : (feasible (standardFloor N V ρ F) C s ν).Nonempty)
    (hν : 0 ≤ ν) (hη : 0 < η)
    (hRT : M.TailResponseRegular C s) (hUEN : M.EdgeNondegenerate signal)
    (hmargin : 4 * (ρ / Real.sqrt N) + ν < signal) (hO : O.Accurate M ρ) :
    let P := parameters N V D L ρ η F C s ν hN hL hF hf1 hgrid
    ∀ (policy : SelectedPackedSampler.Policy N V (Fin (PackedSampler.colorCount D)) State P.repetitions)
      (initialMemory : PackedSampler.InitialReply (N := N) (V := V) → State),
    (SelectedPackedSampler.sampler P policy initialMemory).seedRisk
      (PackedSampler.seedLaw (Color := Fin (PackedSampler.colorCount D)) P).toMeasure M O ≤ ρ + η := by
  intro P policy initialMemory
  have hs := standard_selected_spec ρ F C s ν hF hf1 hgrid
  exact (SelectedPackedSampler.manuscript_finite_hellinger_upper M O D L _ C s ν signal ρ η
    hN hD hL hs.2.2.2.1 hν hs.1.le hs.2.1 hRT hUEN hs.2.2.1 hmargin hη hO policy initialMemory).1

/-- The grid-selected sampler has measurable losses for every frozen map
and the same bound on the actual supremum over the full Hellinger oracle
class. The exact oracle witnesses nonemptiness of that supremum. -/
theorem grid_robustRisk_le (M : ForestModel N V)
    (D L : ℕ) (ρ η F C s ν signal : ℝ)
    (hN : 0 < N) (hD : 9 ≤ D) (hL : 0 < L) (hF : 1 ≤ F)
    (hf1 : standardFloor N V ρ F ≤ 1)
    (hgrid : (feasible (standardFloor N V ρ F) C s ν).Nonempty)
    (hν : 0 ≤ ν) (hη : 0 < η) (hr0 : 0 ≤ ρ) (hr1 : ρ ≤ 1)
    (hRT : M.TailResponseRegular C s) (hUEN : M.EdgeNondegenerate signal)
    (hmargin : 4 * (ρ / Real.sqrt N) + ν < signal) :
    let P := parameters N V D L ρ η F C s ν hN hL hF hf1 hgrid
    ∀ (policy : SelectedPackedSampler.Policy N V (Fin (PackedSampler.colorCount D)) State P.repetitions)
      (initialMemory : PackedSampler.InitialReply (N := N) (V := V) → State),
    let A := SelectedPackedSampler.sampler P policy initialMemory
    let μ := (PackedSampler.seedLaw (Color := Fin (PackedSampler.colorCount D)) P).toMeasure
    A.RiskMeasurable μ M ρ ∧ A.robustRisk μ M ρ ≤ ρ + η := by
  dsimp only
  intro policy initialMemory
  constructor
  · intro O
    exact (measurable_of_finite _).aestronglyMeasurable
  · let : Nonempty (FrozenOracle.Class M ρ) :=
      ⟨⟨FrozenOracle.exact M, FrozenOracle.exact_accurate M hN hr0 hr1⟩⟩
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨O, rfl⟩
    exact grid_seedRisk_le M O.1 D L ρ η F C s ν signal hN hD hL hF hf1 hgrid
      hν hη hRT hUEN hmargin O.2 policy initialMemory

/-- The same original grid selection supplies the concrete forward-KL
bound, using the original public radius for screening and calibration. -/
theorem grid_seedKLRisk_le (M : ForestModel N V) (O : FrozenOracle N V)
    (D L : ℕ) (ρ κ η F C s ν signal : ℝ)
    (hN : 0 < N) (hD : 9 ≤ D) (hL : 0 < L) (hF : 1 ≤ F)
    (hf1 : standardFloor N V ρ F ≤ 1)
    (hgrid : (feasible (standardFloor N V ρ F) C s ν).Nonempty)
    (hν : 0 ≤ ν) (hη : 0 < η) (hr0 : 0 ≤ ρ) (hr1 : ρ ≤ 1)
    (hRT : M.TailResponseRegular C s) (hUEN : M.EdgeNondegenerate signal)
    (hmargin : 4 * (ρ / Real.sqrt N) + ν < signal)
    (hO : O.ForwardKLAccurate M κ) (hκ : κ ≤ ρ^2/(N : ℝ)) :
    let P := parameters N V D L ρ η F C s ν hN hL hF hf1 hgrid
    ∀ (policy : SelectedPackedSampler.Policy N V (Fin (PackedSampler.colorCount D)) State P.repetitions)
      (initialMemory : PackedSampler.InitialReply (N := N) (V := V) → State),
    (SelectedPackedSampler.sampler P policy initialMemory).seedKLRisk
      (PackedSampler.seedLaw (Color := Fin (PackedSampler.colorCount D)) P).toMeasure M O ≤
      (N : ℝ) * κ + (N : ℝ) * Real.log (Fintype.card V) * η := by
  intro P policy initialMemory
  have hs := standard_selected_spec ρ F C s ν hF hf1 hgrid
  exact (SelectedPackedSampler.manuscript_finite_kl_upper M O D L _ C s ν signal ρ κ η
    hN hD hL hs.2.2.2.1 hν hs.1.le hs.2.1 hRT hUEN hs.2.2.1 hmargin hη hr0 hr1 hO hκ policy initialMemory).1

end SelectedThresholdGrid
end ForestSampling
