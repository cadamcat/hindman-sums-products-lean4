import Mathlib

namespace HindmanSumsProducts.Framework

/-- A nonnegative real that is nonzero is positive. -/
theorem nonneg_ne_zero_pos {x : ℝ} (h0 : 0 ≤ x) (hne : x ≠ 0) : 0 < x :=
  lt_of_le_of_ne h0 (Ne.symm hne)

end HindmanSumsProducts.Framework
