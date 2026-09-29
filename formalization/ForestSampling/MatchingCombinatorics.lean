import ForestSampling.HardMatching

set_option autoImplicit false

open scoped BigOperators

namespace ForestSampling

universe u

/-!
# Finite perfect matchings and hard-instance priors

Perfect matchings are determined by their mate maps.  Pairing a finite set of
edge labels with two endpoint labels supplies a matching whenever the number
of positions is even.  These facts provide actual finite probability spaces
for the hard-family prior, including the empty matching at length zero.
-/

namespace PerfectMatching

variable {N : ℕ}

/-- Equality of every mate determines equality of perfect matchings. -/
@[ext]
theorem ext {M L : PerfectMatching N} (h : ∀ i, M.mate i = L.mate i) : M = L := by
  cases M
  cases L
  congr
  exact funext h

/-- The map from a matching to its mate function is injective. -/
theorem mate_injective : Function.Injective (mate : PerfectMatching N → Position N → Position N) := by
  intro M L h
  exact ext fun i ↦ congrFun h i

/-- Matchings have decidable equality by comparing their finite mate maps. -/
instance : DecidableEq (PerfectMatching N) := mate_injective.decidableEq

/-- There are finitely many perfect matchings on a finite position set. -/
instance : Finite (PerfectMatching N) := Finite.of_injective mate mate_injective

/-- The finite matching space can be enumerated for finite probability sums. -/
noncomputable instance : Fintype (PerfectMatching N) := Fintype.ofFinite _

/-- Each matching's mate map is a bijection, being its own inverse. -/
theorem mate_bijective (M : PerfectMatching N) : Function.Bijective M.mate :=
  M.mate_mate.bijective

private theorem fin_two_rev_ne_self (b : Fin 2) : b.rev ≠ b := by
  fin_cases b <;> decide

/-- Transfer the pairing that reverses the two endpoint labels along an
explicit equivalence from positions to edge-label/endpoint-label pairs. -/
def ofPairingEquiv {k : ℕ} (e : Position N ≃ Fin k × Fin 2) : PerfectMatching N where
  mate i := e.symm ((e i).1, (e i).2.rev)
  mate_ne_self i hi := by
    have hb := congrArg (fun j ↦ (e j).2) hi
    simp only [Equiv.apply_symm_apply] at hb
    exact fin_two_rev_ne_self (e i).2 hb
  mate_mate i := by simp

/-- Every even sequence length admits a matching; the construction also covers
`N = 0`, whose position set and matching are empty. -/
theorem nonempty_of_even (hN : Even N) : Nonempty (PerfectMatching N) := by
  obtain ⟨k, hk⟩ := hN
  have hNk : N = k * 2 := by omega
  exact ⟨ofPairingEquiv ((finCongr hNk).trans finProdFinEquiv.symm)⟩

/-- Relabel a matching by conjugating its mate map with a position permutation. -/
def relabel (M : PerfectMatching N) (e : Equiv.Perm (Position N)) : PerfectMatching N where
  mate i := e (M.mate (e.symm i))
  mate_ne_self i hi := by
    apply M.mate_ne_self (e.symm i)
    exact e.injective (by simpa using hi)
  mate_mate i := by
    simp only [Equiv.symm_apply_apply]
    rw [M.mate_mate (e.symm i), e.apply_symm_apply]

@[simp]
theorem relabel_mate (M : PerfectMatching N) (e : Equiv.Perm (Position N)) (i : Position N) :
    (M.relabel e).mate i = e (M.mate (e.symm i)) := rfl

/-- Undoing a relabeling restores the original matching. -/
@[simp]
theorem relabel_symm_relabel (M : PerfectMatching N) (e : Equiv.Perm (Position N)) :
    (M.relabel e).relabel e.symm = M := by
  ext i
  simp

/-- Position relabeling gives a bijection of the finite matching space. -/
def relabelEquiv (e : Equiv.Perm (Position N)) : Equiv.Perm (PerfectMatching N) where
  toFun M := M.relabel e
  invFun M := M.relabel e.symm
  left_inv M := M.relabel_symm_relabel e
  right_inv M := by simpa using M.relabel_symm_relabel e.symm

end PerfectMatching

namespace FinDist

variable (α : Type u) [Fintype α] [Nonempty α]

/-- The uniform probability distribution on an inhabited finite type. -/
noncomputable def uniform : FinDist α where
  mass _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_mass := by
    simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_ne_zero]

@[simp]
theorem uniform_apply (x : α) : uniform α x = (Fintype.card α : ℝ)⁻¹ := rfl

/-- Every point of the finite uniform distribution has positive mass. -/
theorem uniform_strictlyPositive : (uniform α).StrictlyPositive := by
  intro x
  exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)

end FinDist

namespace PerfectMatching

variable {N : ℕ}

/-- The uniform matching prior is defined whenever the position count is even. -/
noncomputable def uniform (hN : Even N) : FinDist (PerfectMatching N) := by
  letI := nonempty_of_even hN
  exact FinDist.uniform _

@[simp]
theorem uniform_apply (hN : Even N) (M : PerfectMatching N) :
    uniform hN M = (Fintype.card (PerfectMatching N) : ℝ)⁻¹ := rfl


/-- The uniform matching law is invariant under every position relabeling. -/
theorem uniform_map_relabel (hN : Even N) (e : Equiv.Perm (Position N)) :
    (uniform hN).map (relabelEquiv e) = uniform hN := by
  classical
  ext M
  rw [FinDist.map_equiv_apply]
  rfl

/-- Jointly relabeling a vertex and its prospective mate preserves edge
probability under the uniform matching law. -/
theorem uniform_mate_relabel (hN : Even N) (e : Equiv.Perm (Position N))
    (i j : Position N) :
    (uniform hN).eventMass (fun M ↦ M.mate (e i) = e j) =
      (uniform hN).eventMass (fun M ↦ M.mate i = j) := by
  classical
  have htransport := (uniform hN).map_equiv_eventMass (relabelEquiv e)
    (fun M ↦ M.mate (e i) = e j)
  rw [uniform_map_relabel] at htransport
  refine htransport.trans ?_
  apply FinDist.eventMass_congr
  intro M
  simp [relabelEquiv, relabel]

/-- Every vertex distinct from a fixed vertex has the same probability of
being its mate, by swapping the two prospective mates. -/
theorem uniform_mate_eq_of_ne (hN : Even N) (i j k : Position N)
    (hij : i ≠ j) (hik : i ≠ k) :
    (uniform hN).eventMass (fun M ↦ M.mate i = j) =
      (uniform hN).eventMass (fun M ↦ M.mate i = k) := by
  have he := uniform_mate_relabel hN (Equiv.swap j k) i j
  simpa only [Equiv.swap_apply_of_ne_of_ne hij hik, Equiv.swap_apply_left] using he.symm

/-- A perfect matching never pairs a vertex with itself. -/
theorem uniform_mate_self (hN : Even N) (i : Position N) :
    (uniform hN).eventMass (fun M ↦ M.mate i = i) = 0 := by
  unfold FinDist.eventMass
  apply Finset.sum_eq_zero
  intro M _
  rw [if_neg (M.mate_ne_self i)]

/-- The probabilities of all possible mates sum to one. -/
theorem sum_uniform_mate (hN : Even N) (i : Position N) :
    (∑ j, (uniform hN).eventMass (fun M ↦ M.mate i = j)) = 1 := by
  unfold FinDist.eventMass
  rw [Finset.sum_comm]
  calc
    (∑ M, ∑ j, if M.mate i = j then uniform hN M else 0) = ∑ M, uniform hN M := by
      apply Finset.sum_congr rfl
      intro M _
      simp
    _ = 1 := (uniform hN).sum_mass

/-- In a uniformly random perfect matching, a fixed vertex's mate is uniform
among the other `N - 1` vertices. -/
theorem uniform_mate_probability (hN : Even N) (i j : Position N) (hij : i ≠ j) :
    (uniform hN).eventMass (fun M ↦ M.mate i = j) = 1 / ((N - 1 : ℕ) : ℝ) := by
  let mass : Position N → ℝ := fun k ↦ (uniform hN).eventMass (fun M ↦ M.mate i = k)
  have hzero : mass i = 0 := uniform_mate_self hN i
  have hconstant : ∀ k ∈ Finset.univ.erase i, mass k = mass j := by
    intro k hk
    exact uniform_mate_eq_of_ne hN i k j (Finset.mem_erase.mp hk).1.symm hij
  have hsum : ((N - 1 : ℕ) : ℝ) * mass j = 1 := by
    calc
      ((N - 1 : ℕ) : ℝ) * mass j = ∑ _k ∈ Finset.univ.erase i, mass j := by
        simp [nsmul_eq_mul]
      _ = ∑ k ∈ Finset.univ.erase i, mass k := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (hconstant k hk).symm
      _ = ∑ k, mass k := by
        simpa only [hzero, add_zero] using
          (Finset.sum_erase_add Finset.univ mass (Finset.mem_univ i))
      _ = 1 := sum_uniform_mate hN i
  have hNtwo : 2 ≤ N := by
    by_contra h
    apply hij
    apply Fin.ext
    omega
  have hden : ((N - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : N - 1 ≠ 0)
  apply (eq_div_iff hden).2
  simpa [mul_comm] using hsum

end PerfectMatching

namespace HardMatching

/-- An even position count and a nonempty private-trigger bank give an
inhabited hard-instance index set. -/
theorem instanceIndex_nonempty {N K : ℕ} (hN : Even N) (hK : 1 ≤ K) :
    Nonempty (InstanceIndex N K) := by
  obtain ⟨M⟩ := PerfectMatching.nonempty_of_even hN
  exact ⟨(M, fun _ ↦ ⟨0, hK⟩)⟩

/-- The finite uniform prior jointly randomizes the hidden matching and every
private trigger.  This definition introduces no assumption about a sampler. -/
noncomputable def uniformInstancePrior {N K : ℕ} (hN : Even N) (hK : 1 ≤ K) :
    FinDist (InstanceIndex N K) := by
  letI := instanceIndex_nonempty hN hK
  exact FinDist.uniform _

@[simp]
theorem uniformInstancePrior_apply {N K : ℕ} (hN : Even N) (hK : 1 ≤ K)
    (I : InstanceIndex N K) :
    uniformInstancePrior hN hK I = (Fintype.card (InstanceIndex N K) : ℝ)⁻¹ := rfl


/-- The uniform law of one private trigger in a nonempty bank. -/
noncomputable def uniformTriggerPrior {K : ℕ} (hK : 1 ≤ K) : FinDist (Fin K) := by
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  exact FinDist.uniform _

@[simp]
theorem uniformTriggerPrior_apply {K : ℕ} (hK : 1 ≤ K) (a : Fin K) :
    uniformTriggerPrior hK a = (K : ℝ)⁻¹ := by
  simp [uniformTriggerPrior]

/-- The uniform hard-instance law factors into an independent uniform matching
and independent uniform private triggers at all positions. -/
theorem uniformInstancePrior_eq_product {N K : ℕ} (hN : Even N) (hK : 1 ≤ K) :
    uniformInstancePrior hN hK =
      (PerfectMatching.uniform hN).prod
        (FinDist.piProduct fun _ : Position N ↦ uniformTriggerPrior hK) := by
  ext I
  simp [uniformInstancePrior_apply, FinDist.prod_apply, FinDist.piProduct_apply,
    Fintype.card_prod, Nat.cast_mul, Nat.cast_pow,
    mul_inv_rev, mul_comm]

end HardMatching

end ForestSampling
