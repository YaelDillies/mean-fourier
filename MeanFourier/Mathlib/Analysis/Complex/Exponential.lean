module

public import Mathlib.Analysis.Complex.Exponential

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Positivity

public section

open Real

/-- `(1 + x / n) ^ n ≤ exp x` for `-n ≤ x`. -/
lemma Real.one_add_div_pow_le_exp {n : ℕ} {x : ℝ} (hx : -n ≤ x) : (1 + x / n) ^ n ≤ exp x := by
  simpa [neg_div, sub_neg_eq_add] using one_sub_div_pow_le_exp_neg (t := -x) (by linarith)

variable {d m : ℕ}

private lemma sum_choose_mul_pow_le_add_one_pow {t : ℝ} (ht : 0 ≤ t) (hdm : d ≤ m) :
    ∑ i ∈ .range (d + 1), (m.choose i : ℝ) * t ^ i ≤ (1 + t) ^ m :=
  calc ∑ i ∈ .range (d + 1), (m.choose i : ℝ) * t ^ i
      ≤ ∑ i ∈ .range (m + 1), (m.choose i : ℝ) * t ^ i := by gcongr with i hi
    _ = (1 + t) ^ m := by
        rw [add_comm 1 t, add_pow]
        congr! 1 with i
        ring

private lemma sum_choose_le_mul_sum_choose_mul_pow (hd : (0 : ℝ) < d) (hm : (0 : ℝ) < m)
    (hdm : (d : ℝ) ≤ m) :
    ∑ i ∈ .range (d + 1), (m.choose i : ℝ) ≤
      (m / d : ℝ) ^ d * ∑ i ∈ .range (d + 1), (m.choose i : ℝ) * (d / m : ℝ) ^ i := by
  calc ∑ i ∈ .range (d + 1), (m.choose i : ℝ)
    _ = ∑ i ∈ .range (d + 1), (m.choose i : ℝ) * (d / m : ℝ) ^ i * (m / d : ℝ) ^ i :=
        Finset.sum_congr rfl fun i _ ↦ by
          rw [mul_assoc, ← mul_pow, show (d : ℝ) / m * (m / d) = 1 by field_simp, one_pow,
            mul_one]
    _ ≤ ∑ i ∈ .range (d + 1), (m.choose i : ℝ) * (d / m : ℝ) ^ i * (m / d : ℝ) ^ d := by
        gcongr with i hi
        · exact (one_le_div₀ hd).2 hdm
        · exact Finset.mem_range_succ_iff.1 hi
    _ = (m / d : ℝ) ^ d * ∑ i ∈ .range (d + 1), (m.choose i : ℝ) * (d / m : ℝ) ^ i := by
        rw [← Finset.sum_mul, mul_comm]

/-- For `d ≤ m`, the number of subsets of size at most `d` of an `m`-element set,
`∑ i ≤ d, m.choose i`, is at most `(exp 1 / d * m) ^ d`. -/
lemma sum_choose_le_exp_pow (hdm : d ≤ m) :
    ∑ i ∈ .range (d + 1), (m.choose i : ℝ) ≤ (exp 1 / d * m) ^ d := by
  obtain rfl | hd := d.eq_zero_or_pos
  · simp
  have hm : (0 : ℝ) < m := mod_cast hd.trans_le hdm
  calc ∑ i ∈ .range (d + 1), (m.choose i : ℝ)
      ≤ (m / d : ℝ) ^ d * ∑ i ∈ .range (d + 1), (m.choose i : ℝ) * (d / m : ℝ) ^ i :=
        sum_choose_le_mul_sum_choose_mul_pow (mod_cast hd) hm (mod_cast hdm)
    _ ≤ (m / d : ℝ) ^ d * (1 + d / m : ℝ) ^ m := by
        gcongr; exact sum_choose_mul_pow_le_add_one_pow (by positivity) hdm
    _ ≤ (m / d : ℝ) ^ d * exp 1 ^ d := by
        gcongr
        rw [← Real.exp_nat_mul, mul_one]
        exact Real.one_add_div_pow_le_exp ((neg_nonpos.2 m.cast_nonneg).trans d.cast_nonneg)
    _ = (exp 1 / d * m) ^ d := by ring
