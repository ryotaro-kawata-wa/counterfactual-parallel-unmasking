import ForestSampling.OracleBudgets

set_option autoImplicit false

namespace ForestSampling
namespace Program

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- A stronger lower-bound observation model: current-history marginal reads
are free, while other probes and all nonempty commits retain their charges.
This permits simulation of commit-row feedback without an extra paper query. -/
noncomputable def WithinFreeMarginalBudgets (O : FrozenOracle N V) :
    {h : History N V} → Program N V h → ℕ → ℕ → Prop
  | _, .done _, _, _ => True
  | h, .query state _ next, Q, R =>
      if state = MaskedState.commitState h then
        WithinFreeMarginalBudgets O (next (O.readState state)) Q R
      else 0 < Q ∧ WithinFreeMarginalBudgets O (next (O.readState state)) (Q-1) R
  | _, .commit _ _ _ next, Q, R =>
      0 < R ∧ ∀ z, WithinFreeMarginalBudgets O (next z) Q (R-1)

/-- Enlarging either public budget preserves admissibility in the stronger
observation model. No oracle reply is changed by this implication. -/
theorem WithinFreeMarginalBudgets.mono (O : FrozenOracle N V)
    {h : History N V} {p : Program N V h} {Q R Q' R' : ℕ}
    (hb : p.WithinFreeMarginalBudgets O Q R) (hQ : Q ≤ Q') (hR : R ≤ R') :
    p.WithinFreeMarginalBudgets O Q' R' := by
  induction p generalizing Q R Q' R' with
  | done complete => trivial
  | @query h state respects next ih =>
      simp only [WithinFreeMarginalBudgets] at hb ⊢
      split_ifs at hb ⊢ with he
      · exact ih _ hb hQ hR
      · exact ⟨by omega, ih _ hb.2 (by omega) hR⟩
  | commit batch nonempty fresh next ih =>
      exact ⟨by exact lt_of_lt_of_le hb.1 hR,
        fun z ↦ ih z (hb.2 z) hQ (by omega)⟩

/-- Ordinary actual-oracle budgets imply the relaxed observation budgets.
This implication is in the direction needed for a stronger lower bound. -/
theorem WithinOracleBudgets.withinFreeMarginalBudgets (O : FrozenOracle N V)
    {h : History N V} {p : Program N V h} {Q R : ℕ}
    (hb : p.WithinOracleBudgets O Q R) : p.WithinFreeMarginalBudgets O Q R := by
  induction p generalizing Q R with
  | done complete => trivial
  | @query h state respects next ih =>
      simp only [WithinFreeMarginalBudgets]
      split_ifs
      · exact (ih _ hb.2).mono O (Nat.sub_le _ _) le_rfl
      · exact ⟨hb.1, ih _ hb.2⟩
  | commit batch nonempty fresh next ih =>
      exact ⟨hb.1, fun z ↦ ih z (hb.2 z)⟩

/-- Free marginal observations leave the actual number of commit rounds
bounded on every retained path, including analytic midpoint paths. -/
theorem retainedRoundCount_le_freeMarginalBudget (O : FrozenOracle N V)
    {h : History N V} (p : Program N V h) (path : RetainedPath O p)
    (Q R : ℕ) (hb : p.WithinFreeMarginalBudgets O Q R) :
    retainedRoundCount O p path ≤ R := by
  induction p generalizing Q R with
  | done complete => exact Nat.zero_le _
  | @query h state respects next ih =>
      simp only [WithinFreeMarginalBudgets] at hb
      split_ifs at hb
      · exact ih _ path Q R hb
      · exact ih _ path (Q-1) R hb.2
  | commit batch nonempty fresh next ih =>
      have hh := ih path.1 path.2 Q (R-1) (hb.2 path.1)
      change 1 + retainedRoundCount O (next path.1) path.2 ≤ R
      have hpos : 0 < R := hb.1
      omega

/-- Marginal feedback cannot complete any new coordinate without a commit. -/
theorem complete_of_freeMarginalBudget_zero (O : FrozenOracle N V)
    {h : History N V} (p : Program N V h) (Q : ℕ)
    (hb : p.WithinFreeMarginalBudgets O Q 0) : h.committed = Finset.univ := by
  induction p generalizing Q with
  | done complete => exact complete
  | @query h state respects next ih =>
      simp only [WithinFreeMarginalBudgets] at hb
      split_ifs at hb
      · exact ih _ Q hb
      · exact ih _ (Q-1) hb.2
  | commit batch nonempty fresh next ih => exact (Nat.not_lt_zero 0 hb.1).elim

end Program
namespace Sampler

variable {N : ℕ} {V Seed : Type*} [Fintype V] [DecidableEq V]

/-- The same seed and distinguished preprocessing conventions with free
current-history marginal feedback, uniformly over all actual paths. -/
def WithinFreeMarginalBudgets (A : Sampler N V Seed) (O : FrozenOracle N V) (Q R : ℕ) : Prop :=
  ∀ w, (A.program w (O.readState (MaskedState.allMask N V))).WithinFreeMarginalBudgets O Q R

end Sampler
end ForestSampling
