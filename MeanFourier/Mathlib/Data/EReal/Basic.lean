module

public import Mathlib.Data.EReal.Basic
public import Mathlib.Basic.Real.ENatENNReal

public section

lemma ENat.natCast_toNat_le_of_ennrealToEReal_toENNReal_le_realToEReal {n : ℕ∞} {K : ℝ}
    (h : (n : EReal) ≤ K) : n.toNat ≤ K := by
  lift n to ℕ using fun hn ↦ by simp [hn] at h
  simp only [ENat.toNat_natCast]
  change ((n : ℝ) : EReal) ≤ K at h
  exact_mod_cast h
