module

public import Mathlib.Data.EReal.Basic

public section

namespace EReal

open scoped ENNReal

@[simp] lemma ennrealtoEReal_le_natCast {r : ℝ≥0∞} {n : ℕ} : (r : EReal) ≤ n ↔ r ≤ n := by
  rw [← EReal.coe_ennreal_le_coe_ennreal_iff]; rfl

end EReal
