import ForestSampling.LocalMarkov
import ForestSampling.FiniteKL
import ForestSampling.FiniteMarkovChain
import ForestSampling.PathGraph

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace PathClass

/-- The comparison vocabulary consists of two named tokens and a positive
number of background tokens. Its cardinality is `B+2`. -/
abbrev Token (B : ℕ) := Option (Option (Fin B))

/-- Finite parameters for the manuscript's two-type comparison chain.
The eventual choice is `p=2^(-exponent)` with `exponent>1`. -/
structure Parameters (B : ℕ) where
  p : ℝ
  p_pos : 0 < p
  p_lt_half : p < 1 / 2
  background_pos : 0 < B

variable {B : ℕ}

namespace Parameters

noncomputable section

def tokenMass (P : Parameters B) : Token B → ℝ
  | none => 1 - P.p
  | some none => P.p / 2
  | some (some _) => P.p / (2 * B)

theorem tokenMass_pos (P : Parameters B) (a : Token B) : 0 < P.tokenMass a := by
  cases a with
  | none => simp only [tokenMass]; linarith [P.p_lt_half]
  | some a =>
      cases a with
      | none => exact div_pos P.p_pos (by norm_num)
      | some b => exact div_pos P.p_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr P.background_pos))

theorem tokenMass_sum (P : Parameters B) : ∑ a, P.tokenMass a = 1 := by
  simp only [Fintype.sum_option, tokenMass, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hB : (B : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr P.background_pos)
  field_simp
  ring

/-- The actual full-vocabulary stationary marginal. -/
def marginal (P : Parameters B) : FinDist (Token B) where
  mass := P.tokenMass
  nonneg a := (P.tokenMass_pos a).le
  sum_mass := P.tokenMass_sum

@[simp] theorem marginal_apply (P : Parameters B) (a : Token B) : P.marginal a = P.tokenMass a := rfl

theorem marginal_positive (P : Parameters B) : P.marginal.StrictlyPositive := P.tokenMass_pos

/-- `false` is type A (the first token), and `true` is type B (all other tokens). -/
def tokenType : Token B → Bool
  | none => false
  | some _ => true

def typeMass (P : Parameters B) : Bool → ℝ
  | false => 1 - P.p
  | true => P.p

theorem typeMass_pos (P : Parameters B) (t : Bool) : 0 < P.typeMass t := by
  cases t <;> simp only [typeMass]
  · linarith [P.p_lt_half]
  · exact P.p_pos

def typeJointMass (P : Parameters B) : Bool → Bool → ℝ
  | false, false => 1 - 3 * P.p / 2
  | _, _ => P.p / 2

theorem typeJointMass_pos (P : Parameters B) (s t : Bool) : 0 < P.typeJointMass s t := by
  cases s <;> cases t <;> simp only [typeJointMass] <;> linarith [P.p_pos, P.p_lt_half]

theorem typeJointMass_symmetric (P : Parameters B) (s t : Bool) :
    P.typeJointMass s t = P.typeJointMass t s := by cases s <;> cases t <;> rfl

theorem typeJointMass_row_sum (P : Parameters B) (s : Bool) :
    (∑ t, P.typeJointMass s t) = P.typeMass s := by
  cases s <;> simp only [Fintype.sum_bool, typeJointMass, typeMass] <;> ring

/-- The positive symmetric two-type interaction table from the manuscript. -/
def interaction (P : Parameters B) (s t : Bool) : ℝ :=
  P.typeJointMass s t / (P.typeMass s * P.typeMass t)

theorem interaction_pos (P : Parameters B) (s t : Bool) : 0 < P.interaction s t :=
  div_pos (P.typeJointMass_pos s t) (mul_pos (P.typeMass_pos s) (P.typeMass_pos t))

theorem interaction_symmetric (P : Parameters B) (s t : Bool) :
    P.interaction s t = P.interaction t s := by
  simp only [interaction, P.typeJointMass_symmetric s t, mul_comm]

/-- Grouping the full token marginal by its actual two-type map recovers
the prescribed type masses, uniformly in the background vocabulary size. -/
theorem marginal_type_sum (P : Parameters B) (f : Bool → ℝ) :
    (∑ a, P.marginal a * f (tokenType a)) = ∑ t, P.typeMass t * f t := by
  simp only [Fintype.sum_option, marginal_apply, tokenMass, tokenType, Fintype.sum_bool,
    typeMass, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hB : (B : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr P.background_pos)
  field_simp
  ring

theorem interaction_row_normalized (P : Parameters B) (s : Bool) :
    (∑ t, P.typeMass t * P.interaction s t) = 1 := by
  have hs := ne_of_gt (P.typeMass_pos s)
  calc
    _ = (∑ t, P.typeJointMass s t) / P.typeMass s := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro t _
      have ht := ne_of_gt (P.typeMass_pos t)
      unfold interaction
      field_simp
    _ = 1 := by rw [P.typeJointMass_row_sum, div_self hs]

/-- The actual token transition law `K(y|x)=pi(y)*g(type(x),type(y))`. -/
def kernel (P : Parameters B) (x : Token B) : FinDist (Token B) where
  mass y := P.marginal y * P.interaction (tokenType x) (tokenType y)
  nonneg y := mul_nonneg (P.marginal.nonneg y) (P.interaction_pos _ _).le
  sum_mass := by rw [P.marginal_type_sum]; exact P.interaction_row_normalized _

@[simp] theorem kernel_apply (P : Parameters B) (x y : Token B) :
    P.kernel x y = P.marginal y * P.interaction (tokenType x) (tokenType y) := rfl

theorem kernel_positive (P : Parameters B) (x : Token B) : (P.kernel x).StrictlyPositive :=
  fun y ↦ mul_pos (P.marginal_positive y) (P.interaction_pos _ _)

/-- Detailed balance is proved on the actual token laws, not only on the
two-type table; it supplies endpoint compatibility for the path model. -/
theorem detailed_balance (P : Parameters B) (x y : Token B) :
    P.marginal x * P.kernel x y = P.marginal y * P.kernel y x := by
  simp only [kernel_apply]
  rw [P.interaction_symmetric (tokenType y) (tokenType x)]
  ring

theorem stationary (P : Parameters B) (y : Token B) :
    (∑ x, P.marginal x * P.kernel x y) = P.marginal y := by
  simp_rw [P.detailed_balance]
  rw [← Finset.mul_sum, (P.kernel y).sum_mass, mul_one]

/-- The two-type table has a strictly positive determinant, so its adjacent
type variables cannot be independent. -/
theorem typeJoint_determinant (P : Parameters B) :
    P.typeJointMass false false * P.typeJointMass true true -
      P.typeJointMass false true * P.typeJointMass true false = P.p * (1 - 2 * P.p) / 2 := by
  simp only [typeJointMass]
  ring

theorem typeJoint_determinant_pos (P : Parameters B) :
    0 < P.typeJointMass false false * P.typeJointMass true true -
      P.typeJointMass false true * P.typeJointMass true false := by
  rw [P.typeJoint_determinant]
  exact div_pos (mul_pos P.p_pos (by linarith [P.p_lt_half])) (by norm_num)

/-- Marginal odds times the type-A neighbor ratio. The corresponding
type-B factor is exactly one, so the response simplifies to this scalar. -/
def scaledOdds (P : Parameters B) : ℝ := (2 - 3 * P.p) / P.p

def otherOddsA (P : Parameters B) : ℝ := (2 - 3 * P.p) / (1 - P.p)

def otherOddsB (P : Parameters B) : ℝ := P.p / (1 - P.p)

theorem scaledOdds_gt_one (P : Parameters B) : 1 < P.scaledOdds := by
  rw [scaledOdds, lt_div_iff₀ P.p_pos]
  linarith [P.p_lt_half]

theorem otherOddsA_pos (P : Parameters B) : 0 < P.otherOddsA :=
  div_pos (by linarith [P.p_lt_half]) (by linarith [P.p_lt_half])

theorem otherOddsB_pos (P : Parameters B) : 0 < P.otherOddsB :=
  div_pos P.p_pos (by linarith [P.p_lt_half])

/-- The exact difference of type-A probabilities after changing one
neighbor from type B to A, with the other-neighbor odds contribution `q`. -/
def response (P : Parameters B) (q : ℝ) : ℝ :=
  P.scaledOdds * q / (1 + P.scaledOdds * q) - q / (1 + q)

theorem response_formula (P : Parameters B) (q : ℝ) (hq : 0 ≤ q) :
    P.response q = (P.scaledOdds - 1) * q /
      ((1 + P.scaledOdds * q) * (1 + q)) := by
  have hA : 0 < P.scaledOdds := lt_trans zero_lt_one P.scaledOdds_gt_one
  have hden : 0 < 1 + P.scaledOdds * q := by positivity
  have hqden : 0 < 1 + q := by positivity
  unfold response
  field_simp
  ring

theorem response_pos (P : Parameters B) (q : ℝ) (hq : 0 < q) : 0 < P.response q := by
  rw [P.response_formula q hq.le]
  have hA : 0 < P.scaledOdds := lt_trans zero_lt_one P.scaledOdds_gt_one
  exact div_pos (mul_pos (sub_pos.mpr P.scaledOdds_gt_one) hq) (by positivity)

/-- A direct positive-polynomial proof of the RT scalar bound avoids any
optimization or differentiability premise. It holds for every positive
other-neighbor odds contribution, not just the path's three possibilities. -/
theorem response_le_one_sub_p (P : Parameters B) (q : ℝ) (hq : 0 ≤ q) :
    P.response q ≤ 1 - P.p := by
  rw [P.response_formula q hq]
  have hA : 0 < P.scaledOdds := lt_trans zero_lt_one P.scaledOdds_gt_one
  have hrel : P.p * P.scaledOdds = 2 - 3 * P.p := by
    unfold scaledOdds
    field_simp [ne_of_gt P.p_pos]
  have hrelq : P.p * P.scaledOdds * q = (2 - 3 * P.p) * q := by rw [hrel]
  apply (div_le_iff₀ (by positivity : 0 < (1 + P.scaledOdds * q) * (1 + q))).mpr
  have hrest : 0 ≤ (1 - P.p) * P.scaledOdds * q ^ 2 := by
    apply mul_nonneg
    · exact mul_nonneg (by linarith [P.p_lt_half]) hA.le
    · exact sq_nonneg q
  have hpq := mul_nonneg P.p_pos.le hq
  nlinarith [P.p_lt_half]

/-- The same positive constant works at an endpoint or an interior
readout, since a path has at most one other neighbor. -/
def edgeSignal (P : Parameters B) : ℝ :=
  min (P.response 1) (min (P.response P.otherOddsA) (P.response P.otherOddsB))

theorem edgeSignal_pos (P : Parameters B) : 0 < P.edgeSignal := by
  exact lt_min (P.response_pos 1 zero_lt_one)
    (lt_min (P.response_pos _ P.otherOddsA_pos) (P.response_pos _ P.otherOddsB_pos))

theorem edgeSignal_le_response (P : Parameters B) (q : ℝ)
    (hq : q = 1 ∨ q = P.otherOddsA ∨ q = P.otherOddsB) : P.edgeSignal ≤ P.response q := by
  rcases hq with rfl | rfl | rfl
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem backgroundMass_le_uniform (P : Parameters B) :
    P.p / (2 * B) ≤ 1 / ((B + 2 : ℕ) : ℝ) := by
  have hB : (0 : ℝ) < B := Nat.cast_pos.mpr P.background_pos
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * B) (by positivity)).mpr
  have hpB := mul_nonneg (by linarith [P.p_lt_half] : 0 ≤ 1 / 2 - P.p) hB.le
  have hBone : (1 : ℝ) ≤ B := by exact_mod_cast P.background_pos
  push_cast
  nlinarith [P.p_lt_half]

/-- The normalized, strictly positive full-vocabulary path law, built by
successive transition draws from the stationary initial marginal. -/
def target (P : Parameters B) (N : ℕ) : FinDist (Configuration N (Token B)) :=
  FiniteMarkovChain.law P.marginal P.kernel N

theorem target_positive (P : Parameters B) (N : ℕ) : (P.target N).StrictlyPositive :=
  FiniteMarkovChain.law_positive P.marginal P.kernel P.marginal_positive P.kernel_positive N

theorem target_marginal (P : Parameters B) (N : ℕ) (i : Position N) :
    (P.target N).positionMarginal i = P.marginal :=
  FiniteMarkovChain.stationary_law_marginal P.marginal P.kernel P.stationary N i

theorem target_apply (P : Parameters B) (n : ℕ) (x : Configuration (n + 1) (Token B)) :
    P.target (n + 1) x = P.marginal (x 0) * ∏ i : Fin n, P.kernel (x i.castSucc) (x i.succ) :=
  FiniteMarkovChain.law_apply P.marginal P.kernel n x

/-- The actual chain density satisfies the repository's rooted forest
factorization, including its root marginal and every transition factor. -/
theorem target_factorizes (P : Parameters B) (n : ℕ) :
    ForestFactorization.Holds (P.target (n + 1)) (fun _ _ ↦ P.kernel)
      (SimpleGraph.pathGraph (n + 1)) (PathGraph.rooting (n + 1)) := by
  intro x
  rw [target_apply]
  unfold ForestFactorization.mass
  simp only [PathGraph.roots_succ, Finset.prod_singleton, target_marginal]
  congr 1
  rw [Rooting.nonRoots, PathGraph.roots_succ, Finset.sdiff_eq_filter,
    Finset.prod_filter, Fin.prod_univ_succ]
  simp only [Finset.mem_singleton, not_true_eq_false, ite_false, Fin.succ_ne_zero,
    not_false_eq_true, ite_true, PathGraph.parent_succ, one_mul]

/-- The comparison construction is an actual `ForestModel`, with graph
acyclicity, positive kernels, factorization and endpoint compatibility all
proved from its explicit stationary Markov-chain construction. -/
def model (P : Parameters B) (n : ℕ) : ForestModel (n + 1) (Token B) where
  target := P.target (n + 1)
  target_positive := P.target_positive (n + 1)
  graph := SimpleGraph.pathGraph (n + 1)
  graph_acyclic := PathGraph.isAcyclic (n + 1)
  kernel := fun _ _ ↦ P.kernel
  kernel_positive := fun _ _ _ ↦ P.kernel_positive
  rooting := PathGraph.rooting (n + 1)
  factorizes := P.target_factorizes n
  endpoint_compatible := by
    intro i j _ a b
    simp only [target_marginal]
    exact P.detailed_balance a b

@[simp] theorem model_marginal (P : Parameters B) (n : ℕ) (i : Position (n + 1)) :
    (P.model n).marginal i = P.marginal := P.target_marginal (n + 1) i

end
end Parameters

/-- The comparison proposition's prescribed parameter lies in the exact
positive range needed by every kernel and response calculation. -/
noncomputable def fromExponent (B : ℕ) (exponent : ℝ) (he : 1 < exponent)
    (hB : 0 < B) : Parameters B where
  p := (2 : ℝ) ^ (-exponent)
  p_pos := Real.rpow_pos_of_pos (by norm_num) _
  p_lt_half := by
    have hh := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (by linarith : -exponent < (-1 : ℝ))
    simpa only [Real.rpow_neg_one, inv_eq_one_div] using hh
  background_pos := hB

end PathClass
end ForestSampling
