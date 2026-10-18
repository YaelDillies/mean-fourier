module

public import Mathlib.Analysis.Complex.Exponential

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Positivity

public section

open Real

variable {d m : ℕ}

private lemma sum_choose_mul_pow_le_add_one_pow {t : ℝ} (ht : 0 ≤ t) (hdm : d ≤ m) :
    ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) * t ^ i ≤ (1 + t) ^ m := by
  rw [show (1 + t) ^ m = ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * t ^ i by
    rw [add_comm, add_pow t 1 m]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [one_pow, mul_one]; ring]
  gcongr with i hi

private lemma one_add_div_pow_le_exp_pow : (1 + (d : ℝ) / m) ^ m ≤ exp 1 ^ d := by
  simpa [neg_div, sub_neg_eq_add, ← Real.exp_nat_mul]
    using Real.one_sub_div_pow_le_exp_neg (n := m) (t := -(d : ℝ))
      ((neg_nonpos.2 d.cast_nonneg).trans m.cast_nonneg)

private lemma sum_choose_le_mul_sum_choose_mul_pow (hd : (0 : ℝ) < d) (hm : (0 : ℝ) < m)
    (hdm : (d : ℝ) ≤ m) :
    (∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ)) ≤
      ((m : ℝ) / d) ^ d * ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) * ((d : ℝ) / m) ^ i := by
  rw [Finset.sum_congr rfl fun i _ ↦ show (m.choose i : ℝ)
      = (m.choose i : ℝ) * ((d : ℝ) / m) ^ i * ((m : ℝ) / d) ^ i by
    rw [mul_assoc, ← mul_pow, show (d : ℝ) / m * ((m : ℝ) / d) = 1 by field_simp, one_pow, mul_one]]
  calc ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) * ((d : ℝ) / m) ^ i * ((m : ℝ) / d) ^ i
      ≤ ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) * ((d : ℝ) / m) ^ i * ((m : ℝ) / d) ^ d :=
        Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left
          (pow_right_mono₀ ((le_div_iff₀ hd).mpr (by linarith))
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) (by positivity)
    _ = ((m : ℝ) / d) ^ d * ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) * ((d : ℝ) / m) ^ i := by
        rw [← Finset.sum_mul, mul_comm]

/-- For `0 < d ≤ m`, the number of subsets of size at most `d` of an `m`-element set,
`∑ i ≤ d, m.choose i`, is at most `(exp 1 / d * m) ^ d`. -/
lemma sum_choose_le_exp_pow (d m : ℕ) (hd : 0 < d) (hdm : d ≤ m) :
    (∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ)) ≤ (exp 1 / d * m) ^ d :=
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le hd hdm)
  calc (∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ))
      ≤ ((m : ℝ) / d) ^ d * ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) * ((d : ℝ) / m) ^ i :=
        sum_choose_le_mul_sum_choose_mul_pow (Nat.cast_pos.mpr hd) hm' (Nat.cast_le.mpr hdm)
    _ ≤ ((m : ℝ) / d) ^ d * (1 + (d : ℝ) / m) ^ m :=
        mul_le_mul_of_nonneg_left
          (sum_choose_mul_pow_le_add_one_pow (by positivity) hdm) (by positivity)
    _ ≤ ((m : ℝ) / d) ^ d * exp 1 ^ d :=
        mul_le_mul_of_nonneg_left one_add_div_pow_le_exp_pow (by positivity)
    _ = (exp 1 / d * m) ^ d := by rw [← mul_pow]; ring_nf
