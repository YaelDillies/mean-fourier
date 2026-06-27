module

public import Mathlib.Data.Real.ENatENNReal

public section

namespace ENat
variable {n : ℕ∞}

@[simp] lemma toENNReal_eq_zero : toENNReal n = 0 ↔ n = 0 := by rw [← toENNReal_zero, toENNReal_inj]

@[simp] lemma toEnnreal_le_natCast {m : ℕ∞} {n : ℕ} : toENNReal m ≤ n ↔ m ≤ n := by
  rw [← ENat.toENNReal_le]; rfl

end ENat
