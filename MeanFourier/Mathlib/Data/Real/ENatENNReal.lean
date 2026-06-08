module

public import Mathlib.Data.Real.ENatENNReal

public section

namespace ENat
variable {n : ℕ∞}

@[simp] lemma toENNReal_eq_zero : toENNReal n = 0 ↔ n = 0 := by rw [← toENNReal_zero, toENNReal_inj]

end ENat
