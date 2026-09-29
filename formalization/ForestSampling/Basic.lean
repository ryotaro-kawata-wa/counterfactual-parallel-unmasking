import Mathlib

set_option autoImplicit false

namespace ForestSampling

/-- A minimal theorem used to verify that Lean and Mathlib are available. -/
theorem environment_smoke_test : (1 : ℕ) + 1 = 2 := by
  norm_num

end ForestSampling
