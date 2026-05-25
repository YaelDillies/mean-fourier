module

public import Mathlib.Data.ENat.Basic

public section

namespace ENat
variable {a b : ℕ∞}

lemma mul_eq_top : a * b = ⊤ ↔ a ≠ 0 ∧ b = ⊤ ∨ a = ⊤ ∧ b ≠ 0 := WithTop.mul_eq_top_iff

end ENat
