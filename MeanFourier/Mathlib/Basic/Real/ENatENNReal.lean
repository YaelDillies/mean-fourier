module

public import Mathlib.Basic.Real.ENatENNReal

public section

namespace ENat
variable {n : ℕ∞}

@[simp] lemma toENNReal_le_natCast {m : ℕ∞} {n : ℕ} : toENNReal m ≤ n ↔ m ≤ n := by
  rw [← ENat.toENNReal_le]; rfl

end ENat
