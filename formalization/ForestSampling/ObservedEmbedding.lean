import ForestSampling.ObservedSimulation
import ForestSampling.Minimax

set_option autoImplicit false

namespace ForestSampling

universe u v

namespace ObservedSampler

variable {N : ℕ} {V : Type u} {Seed : Type v} [Fintype V] [DecidableEq V]

/-- Existing controllers are valid full-observation controllers that simply
ignore the additional commit probability rows. -/
def ofSampler (A : Sampler N V Seed) : ObservedSampler N V Seed where
  program w reply := ObservedProgram.ofProgram (A.program w reply)

theorem outputLaw_ofSampler (A : Sampler N V Seed) (w : Seed) (O : FrozenOracle N V) :
    (ofSampler A).outputLaw w O = A.outputLaw w O :=
  ObservedProgram.eval_ofProgram O _

theorem withinOracleBudgets_ofSampler {A : Sampler N V Seed} {O : FrozenOracle N V} {Q R : ℕ}
    (h : A.WithinOracleBudgets O Q R) : (ofSampler A).WithinOracleBudgets O Q R := by
  intro w
  exact ObservedProgram.withinOracleBudgets_ofProgram O (h w)

end ObservedSampler

namespace RandomizedObservedSamplerData

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

def ofSamplerData (A : RandomizedSamplerData N V) : RandomizedObservedSamplerData N V where
  Seed := A.Seed
  seedMeasurableSpace := A.seedMeasurableSpace
  seedMeasure := A.seedMeasure
  seedIsProbability := A.seedIsProbability
  sampler := ObservedSampler.ofSampler A.sampler

theorem risk_ofSamplerData (A : RandomizedSamplerData N V) (I : SamplingInstance N V) :
    (ofSamplerData A).risk I = A.risk I := by
  unfold risk RandomizedSamplerData.risk Sampler.seedRisk
  simp only [ofSamplerData, ObservedSampler.outputLaw_ofSampler]
  rfl

theorem riskMeasurableAt_ofSamplerData_iff (A : RandomizedSamplerData N V)
    (I : SamplingInstance N V) : (ofSamplerData A).RiskMeasurableAt I ↔ A.RiskMeasurableAt I := by
  unfold RiskMeasurableAt RandomizedSamplerData.RiskMeasurableAt
  simp only [ofSamplerData, ObservedSampler.outputLaw_ofSampler]
  rfl

end RandomizedObservedSamplerData

namespace InstanceFamily

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]
variable {ι : Type u} (F : ι → SamplingInstance N V)

/-- A single all-at-once commit witnesses nonemptiness of the actual paper
protocol class, including measurable seed-averaged risk. -/
theorem observedBudgetedSampler_nonempty (Q R : ℕ) (hR : 1 ≤ R) :
    Nonempty (ObservedBudgetedSampler F Q R) := by
  obtain ⟨A⟩ := budgetedSampler_nonempty F Q R hR
  refine ⟨⟨RandomizedObservedSamplerData.ofSamplerData A.1, ?_, ?_⟩⟩
  · intro i
    exact ObservedSampler.withinOracleBudgets_ofSampler
      (Sampler.WithinBudgets.withinOracleBudgets A.2.1 (F i).oracle)
  · intro i
    exact (RandomizedObservedSamplerData.riskMeasurableAt_ofSamplerData_iff A.1 (F i)).mpr (A.2.2 i)

end InstanceFamily
end ForestSampling
