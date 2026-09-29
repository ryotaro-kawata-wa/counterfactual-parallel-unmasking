import ForestSampling.ScreeningPreprocess

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace Screening

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The tail is represented once: the full response diameter loses at most
one tail tolerance, including bank--bank, mixed, and tail--tail cases. -/
theorem full_response_le_bank_add_tail (rows : V → FinDist V) (bank : Finset V)
    (tail : V) (htail : tail ∉ bank) (D ν : ℝ) (hD : 0 ≤ D) (hν : 0 ≤ ν)
    (hbank : ∀ a ∈ insert tail bank, ∀ b ∈ insert tail bank,
      FinDist.tv (rows a) (rows b) ≤ D)
    (htails : ∀ a ∉ bank, ∀ b ∉ bank, FinDist.tv (rows a) (rows b) ≤ ν)
    (a b : V) : FinDist.tv (rows a) (rows b) ≤ D + ν := by
  by_cases ha : a ∈ bank <;> by_cases hb : b ∈ bank
  · exact (hbank a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb)).trans
      (le_add_of_nonneg_right hν)
  · exact (FinDist.tv_triangle (rows a) (rows tail) (rows b)).trans
      (add_le_add (hbank a (Finset.mem_insert_of_mem ha) tail (Finset.mem_insert_self _ _))
        (htails tail htail b hb))
  · rw [FinDist.tv_comm]
    exact (FinDist.tv_triangle (rows b) (rows tail) (rows a)).trans
      (add_le_add (hbank b (Finset.mem_insert_of_mem hb) tail (Finset.mem_insert_self _ _))
        (htails tail htail a ha))
  · exact (htails a ha b hb).trans (le_add_of_nonneg_left hD)

variable {N : ℕ} [Nonempty V]

/-- The actual RT assumption, TV≤1, and feasible public threshold certify
every pair of omitted rows by the clipped tail tolerance. -/
theorem omitted_response_le (M : ForestModel N V) (O : FrozenOracle N V)
    (C s t ε ν : ℝ) (hRT : M.TailResponseRegular C s)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hfeasible : min 1 (C * t ^ s) ≤ ν)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.tv (y.exactRow M.target M.target_positive j) (O.row y j) ≤ ε)
    {i j : Position N} (hij : i ≠ j) (z : CompleteBoundary N V i j)
    (a b : V) (ha : a ∉ tokenBank O t ε i) (hb : b ∉ tokenBank O t ε i) :
    FinDist.tv (M.target.boundaryRow M.target_positive i j a z)
      (M.target.boundaryRow M.target_positive i j b z) ≤ ν := by
  apply (le_min (FinDist.tv_le_one _ _) ?_).trans hfeasible
  exact hRT.2.2 i j hij t ht0 ht1 z a b
    (outside_bank_mem_tail M O t ε hrows i a ha)
    (outside_bank_mem_tail M O t ε hrows i b hb)

variable {Column : Type*} [Fintype Column] [Nonempty Column]

/-- The observable TV diameter across all packed source columns. -/
noncomputable def rowDiameter (observed : Column → FinDist V) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun pair : Column × Column ↦ FinDist.tv (observed pair.1) (observed pair.2))

omit [DecidableEq V] [Nonempty V] in
theorem rowDiameter_gt_iff (observed : Column → FinDist V) (r : ℝ) :
    r < rowDiameter observed ↔ ∃ c d, r < FinDist.tv (observed c) (observed d) := by
  simp [rowDiameter, Finset.lt_sup'_iff]

omit [DecidableEq V] [Nonempty V] in
/-- If exact rows coincide, two noisy rows cannot exceed the strict screen
threshold. This is the no-false-positive comparison for one coloring. -/
theorem rowDiameter_le_of_common_exact (observed : Column → FinDist V)
    (exact : FinDist V) (ε : ℝ)
    (hrows : ∀ c, FinDist.tv exact (observed c) ≤ ε) :
    rowDiameter observed ≤ 2 * ε := by
  apply Finset.sup'_le
  intro pair _
  have h := FinDist.tv_triangle (observed pair.1) exact (observed pair.2)
  rw [FinDist.tv_comm (observed pair.1) exact] at h
  linarith [hrows pair.1, hrows pair.2]

omit [DecidableEq V] [Nonempty V] in
/-- If no observed pair crosses `2ε`, every queried exact pair is within
`4ε`. The two row errors are both accounted for explicitly. -/
theorem exact_pair_le_of_small_observed_diameter (observed exact : Column → FinDist V)
    (ε : ℝ) (hrows : ∀ c, FinDist.tv (exact c) (observed c) ≤ ε)
    (hdiam : rowDiameter observed ≤ 2 * ε) (c d : Column) :
    FinDist.tv (exact c) (exact d) ≤ 4 * ε := by
  have hpair : FinDist.tv (observed c) (observed d) ≤ rowDiameter observed :=
    Finset.le_sup' (fun pair : Column × Column ↦ FinDist.tv (observed pair.1) (observed pair.2))
      (Finset.mem_univ (c, d))
  have hleft := FinDist.tv_triangle (exact c) (observed c) (exact d)
  have hright := FinDist.tv_triangle (observed c) (observed d) (exact d)
  rw [FinDist.tv_comm (observed d) (exact d)] at hright
  linarith [hrows c, hrows d]

/-- UEN plus RT forces the observable packed diameter above the screen
threshold. The coverage hypothesis refers to actual packed column values,
and permits arbitrary padding and empty local banks. -/
theorem rowDiameter_gt_of_edge (M : ForestModel N V)
    {i j : Position N} (hedge : M.graph.Adj i j)
    (z : CompleteBoundary N V i j) (bank : Finset V) (tail : V) (htail : tail ∉ bank)
    (source : Column → V) (observed : Column → FinDist V)
    (hcover : ∀ a ∈ insert tail bank, ∃ c, source c = a)
    (ε ν signal : ℝ) (hε : 0 ≤ ε) (hν : 0 ≤ ν)
    (hUEN : M.EdgeNondegenerate signal) (hmargin : 4 * ε + ν < signal)
    (hrows : ∀ c, FinDist.tv
      (M.target.boundaryRow M.target_positive i j (source c) z) (observed c) ≤ ε)
    (htails : ∀ a ∉ bank, ∀ b ∉ bank, FinDist.tv
      (M.target.boundaryRow M.target_positive i j a z)
      (M.target.boundaryRow M.target_positive i j b z) ≤ ν) :
    2 * ε < rowDiameter observed := by
  by_contra hdiam
  have hdiam' : rowDiameter observed ≤ 2 * ε := le_of_not_gt hdiam
  have hbank : ∀ a ∈ insert tail bank, ∀ b ∈ insert tail bank,
      FinDist.tv (M.target.boundaryRow M.target_positive i j a z)
        (M.target.boundaryRow M.target_positive i j b z) ≤ 4 * ε := by
    intro a ha b hb
    obtain ⟨c, hc⟩ := hcover a ha
    obtain ⟨d, hd⟩ := hcover b hb
    have h := exact_pair_le_of_small_observed_diameter observed
      (fun c ↦ M.target.boundaryRow M.target_positive i j (source c) z) ε hrows hdiam' c d
    simpa [hc, hd] using h
  have hfull : M.directedResponse hedge.ne z ≤ 4 * ε + ν := by
    apply Finset.sup'_le
    intro pair _
    exact full_response_le_bank_add_tail _ bank tail htail (4 * ε) ν
      (by positivity) hν hbank htails pair.1 pair.2
  linarith [hUEN.2.2 hedge z]

/-- An empty bank certifies absence of every incident edge under the same
strict margin; no packed probes are necessary in the all-empty case. -/
theorem not_adj_of_empty_bank (M : ForestModel N V) (O : FrozenOracle N V)
    (C s t ε ν signal : ℝ) (hRT : M.TailResponseRegular C s)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hfeasible : min 1 (C * t ^ s) ≤ ν)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.tv (y.exactRow M.target M.target_positive j) (O.row y j) ≤ ε)
    (hUEN : M.EdgeNondegenerate signal) (hmargin : ν < signal)
    {i j : Position N} (hij : i ≠ j) (z : CompleteBoundary N V i j)
    (hempty : tokenBank O t ε i = ∅) : ¬ M.graph.Adj i j := by
  intro hedge
  have hfull : M.directedResponse hij z ≤ ν := by
    apply Finset.sup'_le
    intro pair _
    exact omitted_response_le M O C s t ε ν hRT ht0 ht1 hfeasible hrows hij z
      pair.1 pair.2 (by simp [hempty]) (by simp [hempty])
  linarith [hUEN.2.2 hedge z]

end Screening
end ForestSampling
