module

public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.Data.Real.ENatENNReal

public section

namespace EReal

open scoped ENNReal

@[simp] lemma ennrealtoEReal_le_natCast {r : ℝ≥0∞} {n : ℕ} : (r : EReal) ≤ n ↔ r ≤ n := by
  rw [← EReal.coe_ennreal_le_coe_ennreal_iff]; rfl

end EReal

lemma ENat.ne_top_of_ennrealToEReal_toENNReal_le_realToEReal {n : ℕ∞} {K : ℝ}
    (h : (n : EReal) ≤ K) : n ≠ ⊤ := by
  intro htop
  rw [htop] at h
  exact not_le_of_gt (EReal.coe_lt_top K) h

lemma ENat.natCast_toNat_le_of_ennrealToEReal_toENNReal_le_realToEReal {n : ℕ∞} {K : ℝ}
    (h : (n : EReal) ≤ K) : n.toNat ≤ K := by
  lift n to ℕ using ENat.ne_top_of_ennrealToEReal_toENNReal_le_realToEReal h
  simp only [ENat.toNat_coe]
  change ((n : ℝ) : EReal) ≤ K at h
  exact_mod_cast h
