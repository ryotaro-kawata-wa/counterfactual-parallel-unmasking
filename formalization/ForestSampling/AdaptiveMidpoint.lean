import ForestSampling.FiniteProbability

set_option autoImplicit false

open scoped BigOperators

namespace ForestSampling

/-!
# Finite adaptive midpoint calculus

The equalities in this file retain each branch label in the outcome.  This
distinction matters: a general `FinDist.bind` can merge different histories,
and its output affinity need not equal the affinity on retained paths.

The midpoint construction and the two-step chain identity are finite
probability facts.  Connecting them to the paper's sampler still requires
the replay equivalence between terminal paths and complete configurations.
-/

namespace FinDist

noncomputable section

universe u v

variable {α : Type u} [Fintype α]

/-- Strictly positive finite laws have positive Hellinger affinity. -/
theorem affinity_pos (p q : FinDist α)
    (hp : p.StrictlyPositive) (hq : q.StrictlyPositive) :
    0 < affinity p q := by
  have hα : Nonempty α := by
    by_contra h
    have : IsEmpty α := not_nonempty_iff.mp h
    have hsum := p.sum_mass
    simp at hsum
  obtain ⟨a⟩ := hα
  have hterm : 0 < Real.sqrt (p a * q a) :=
    Real.sqrt_pos.2 (mul_pos (hp a) (hq a))
  exact hterm.trans_le (Finset.single_le_sum
    (fun x _ ↦ Real.sqrt_nonneg (p x * q x)) (Finset.mem_univ a))

/-- Normalize the geometric mean of two strictly positive finite laws. -/
def midpoint (p q : FinDist α)
    (hp : p.StrictlyPositive) (hq : q.StrictlyPositive) : FinDist α where
  mass x := Real.sqrt (p x * q x) / affinity p q
  nonneg x := div_nonneg (Real.sqrt_nonneg _) (affinity_pos p q hp hq).le
  sum_mass := by
    rw [← Finset.sum_div]
    exact div_self (affinity_pos p q hp hq).ne'

@[simp]
theorem midpoint_apply (p q : FinDist α)
    (hp : p.StrictlyPositive) (hq : q.StrictlyPositive) (x : α) :
    midpoint p q hp hq x = Real.sqrt (p x * q x) / affinity p q := rfl

/-- The midpoint kernel preserves strict positivity on the branch space. -/
theorem midpoint_strictlyPositive (p q : FinDist α)
    (hp : p.StrictlyPositive) (hq : q.StrictlyPositive) :
    (midpoint p q hp hq).StrictlyPositive := by
  intro x
  exact div_pos (Real.sqrt_pos.2 (mul_pos (hp x) (hq x)))
    (affinity_pos p q hp hq)

/-- The local affinity is exactly the normalization factor removed by the
midpoint kernel. -/
theorem midpoint_factorization (p q : FinDist α)
    (hp : p.StrictlyPositive) (hq : q.StrictlyPositive) (x : α) :
    affinity p q * midpoint p q hp hq x = Real.sqrt (p x * q x) := by
  rw [midpoint_apply, mul_div_cancel₀ _ (affinity_pos p q hp hq).ne']

variable {β : α → Type v} [∀ a, Fintype (β a)]

/-- A two-stage joint law retaining its first-stage branch label.

The second outcome type and its law may depend on the first outcome. -/
def sigmaJoint (p : FinDist α) (k : (a : α) → FinDist (β a)) :
    FinDist (Sigma β) where
  mass x := p x.1 * k x.1 x.2
  nonneg x := mul_nonneg (p.nonneg x.1) ((k x.1).nonneg x.2)
  sum_mass := by
    rw [Fintype.sum_sigma]
    calc
      (∑ a, ∑ b, p a * k a b) = ∑ a, p a := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.mul_sum, (k a).sum_mass, mul_one]
      _ = 1 := p.sum_mass

@[simp]
theorem sigmaJoint_apply (p : FinDist α) (k : (a : α) → FinDist (β a))
    (x : Sigma β) : sigmaJoint p k x = p x.1 * k x.1 x.2 := rfl

theorem sigmaJoint_strictlyPositive (p : FinDist α)
    (k : (a : α) → FinDist (β a))
    (hp : p.StrictlyPositive) (hk : ∀ a, (k a).StrictlyPositive) :
    (sigmaJoint p k).StrictlyPositive := by
  intro x
  exact mul_pos (hp x.1) (hk x.1 x.2)

/-- The affinity chain rule on a retained, possibly dependent branch space.

The second-stage kernels can vary arbitrarily with the first-stage outcome;
there is no independence assumption between the two stages. -/
theorem affinity_sigmaJoint (p q : FinDist α)
    (k l : (a : α) → FinDist (β a)) :
    affinity (sigmaJoint p k) (sigmaJoint q l) =
      ∑ a, Real.sqrt (p a * q a) * affinity (k a) (l a) := by
  unfold affinity
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [sigmaJoint_apply]
  rw [show p a * k a b * (q a * l a b) =
    (p a * q a) * (k a b * l a b) by ring]
  exact Real.sqrt_mul (mul_nonneg (p.nonneg a) (q.nonneg a)) _

/-- The two-step adaptive midpoint identity as an explicit finite expectation
of the product of the local affinity factors. -/
theorem adaptive_midpoint_two_step (p q : FinDist α)
    (k l : (a : α) → FinDist (β a))
    (hp : p.StrictlyPositive) (hq : q.StrictlyPositive)
    (hk : ∀ a, (k a).StrictlyPositive)
    (hl : ∀ a, (l a).StrictlyPositive) :
    affinity (sigmaJoint p k) (sigmaJoint q l) =
      ∑ x : Sigma β,
        sigmaJoint (midpoint p q hp hq)
          (fun a ↦ midpoint (k a) (l a) (hk a) (hl a)) x *
        (affinity p q * affinity (k x.1) (l x.1)) := by
  rw [affinity_sigmaJoint, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  simp only [sigmaJoint_apply]
  calc
    Real.sqrt (p a * q a) * affinity (k a) (l a) =
        midpoint p q hp hq a *
          (affinity p q * affinity (k a) (l a)) := by
      rw [← midpoint_factorization p q hp hq a]
      ring
    _ = ∑ b, (midpoint p q hp hq a *
        midpoint (k a) (l a) (hk a) (hl a) b) *
        (affinity p q * affinity (k a) (l a)) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, FinDist.sum_mass, mul_one]

/-- Relabeling a retained outcome by a bijection preserves affinity.
An arbitrary many-to-one output map would not give this equality. -/
theorem affinity_map_equiv {γ : Type v} [Fintype γ] [DecidableEq γ]
    (p q : FinDist α) (e : α ≃ γ) :
    affinity (p.map e) (q.map e) = affinity p q := by
  unfold affinity
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_equiv_apply, map_equiv_apply]
  simp

theorem sqHellinger_map_equiv {γ : Type v} [Fintype γ] [DecidableEq γ]
    (p q : FinDist α) (e : α ≃ γ) :
    sqHellinger (p.map e) (q.map e) = sqHellinger p q := by
  rw [sqHellinger, sqHellinger, affinity_map_equiv]

end

end FinDist

/-!
## Iteration on a finite adaptive tree

Each branch may have a different finite number of outcomes, and its subtree
may depend on the outcome. Leaves therefore allow paths of different lengths.
Both executions use the same tree and differ only in the local draw laws.
-/

/-- Two strictly positive local laws on every node of a finite adaptive tree.

Branch outcomes are numbered by `Fin n`; a paper-specific batch assignment
space can be transported to this numbering by any finite equivalence. -/
inductive MidpointTree where
  | leaf : MidpointTree
  | branch {n : ℕ} (p q : FinDist (Fin n))
      (hp : p.StrictlyPositive) (hq : q.StrictlyPositive)
      (next : Fin n → MidpointTree) : MidpointTree

namespace MidpointTree

/-- A terminal path retains every outcome used to select subsequent branches. -/
def Path : MidpointTree → Type
  | .leaf => Unit
  | .branch _ _ _ _ next => (a : _) × Path (next a)

noncomputable instance pathFintype (T : MidpointTree) : Fintype T.Path := by
  induction T with
  | leaf => exact inferInstanceAs (Fintype Unit)
  | @branch n p q hp hq next ih =>
      letI : ∀ a, Fintype (Path (next a)) := ih
      exact inferInstanceAs (Fintype ((a : Fin n) × Path (next a)))

noncomputable section

/-- Path law obtained from the first local kernel at every visited node. -/
def leftLaw : (T : MidpointTree) → FinDist T.Path
  | .leaf => FinDist.dirac (α := Unit) ()
  | .branch p _ _ _ next => FinDist.sigmaJoint p (fun a ↦ leftLaw (next a))

/-- Path law obtained from the second local kernel at every visited node. -/
def rightLaw : (T : MidpointTree) → FinDist T.Path
  | .leaf => FinDist.dirac (α := Unit) ()
  | .branch _ q _ _ next => FinDist.sigmaJoint q (fun a ↦ rightLaw (next a))

/-- The analytic execution using a normalized midpoint at each visited node. -/
def midpointLaw : (T : MidpointTree) → FinDist T.Path
  | .leaf => FinDist.dirac (α := Unit) ()
  | .branch p q hp hq next =>
      FinDist.sigmaJoint (FinDist.midpoint p q hp hq)
        (fun a ↦ midpointLaw (next a))

/-- Product of the local affinities on one complete adaptive path. -/
def affinityWeight : (T : MidpointTree) → T.Path → ℝ
  | .leaf, _ => 1
  | .branch p q _ _ next, x =>
      FinDist.affinity p q * affinityWeight (next x.1) x.2

theorem affinityWeight_nonneg (T : MidpointTree) (x : T.Path) :
    0 ≤ T.affinityWeight x := by
  induction T with
  | leaf => exact zero_le_one
  | @branch n p q hp hq next ih =>
      exact mul_nonneg (FinDist.affinity_nonneg p q) (ih x.1 x.2)

theorem affinityWeight_le_one (T : MidpointTree) (x : T.Path) :
    T.affinityWeight x ≤ 1 := by
  induction T with
  | leaf => exact le_rfl
  | @branch n p q hp hq next ih =>
      exact mul_le_one₀ (FinDist.affinity_le_one p q)
        (affinityWeight_nonneg (next x.1) x.2) (ih x.1 x.2)

/-- At a terminal path, the geometric mean of its two execution masses is
its midpoint probability times the product of all visited local affinities. -/
theorem path_mass_factorization (T : MidpointTree) (x : T.Path) :
    Real.sqrt (T.leftLaw x * T.rightLaw x) =
      T.midpointLaw x * T.affinityWeight x := by
  induction T with
  | leaf =>
      cases x
      simp [leftLaw, rightLaw, midpointLaw, affinityWeight]
  | @branch n p q hp hq next ih =>
      change Real.sqrt ((p x.1 * (next x.1).leftLaw x.2) *
          (q x.1 * (next x.1).rightLaw x.2)) =
        (FinDist.midpoint p q hp hq x.1 * (next x.1).midpointLaw x.2) *
          (FinDist.affinity p q * (next x.1).affinityWeight x.2)
      rw [show (p x.1 * (next x.1).leftLaw x.2) *
          (q x.1 * (next x.1).rightLaw x.2) =
        (p x.1 * q x.1) *
          ((next x.1).leftLaw x.2 * (next x.1).rightLaw x.2) by ring]
      rw [Real.sqrt_mul (mul_nonneg (p.nonneg x.1) (q.nonneg x.1)), ih x.1 x.2]
      rw [← FinDist.midpoint_factorization p q hp hq x.1]
      ring

/-- Full finite-tree adaptive midpoint identity, allowing both adaptive
branch kernels and different terminal path lengths. -/
theorem affinity_eq_midpoint_expectation (T : MidpointTree) :
    FinDist.affinity T.leftLaw T.rightLaw =
      ∑ x, T.midpointLaw x * T.affinityWeight x := by
  exact Finset.sum_congr rfl (fun x _ ↦ T.path_mass_factorization x)

/-- Squared Hellinger loss is the midpoint expectation of one minus the
accumulated local-affinity product. -/
theorem sqHellinger_eq_midpoint_loss (T : MidpointTree) :
    FinDist.sqHellinger T.leftLaw T.rightLaw =
      ∑ x, T.midpointLaw x * (1 - T.affinityWeight x) := by
  rw [FinDist.sqHellinger, T.affinity_eq_midpoint_expectation]
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, T.midpointLaw.sum_mass]

/-- Transport of the path identity to an output space, with the required
path-reconstruction equivalence supplied explicitly. -/
theorem output_sqHellinger_eq_midpoint_loss
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (T : MidpointTree) (replay : T.Path ≃ Ω) :
    FinDist.sqHellinger (T.leftLaw.map replay) (T.rightLaw.map replay) =
      ∑ x, T.midpointLaw x * (1 - T.affinityWeight x) := by
  rw [FinDist.sqHellinger_map_equiv, T.sqHellinger_eq_midpoint_loss]

end

end MidpointTree

end ForestSampling
