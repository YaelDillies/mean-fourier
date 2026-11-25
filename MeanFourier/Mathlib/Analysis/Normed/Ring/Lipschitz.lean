module

public import Mathlib.Analysis.Normed.Ring.Basic
public import MeanFourier.Mathlib.Topology.MetricSpace.Pseudo.Defs

import Mathlib.Tactic.NoncommRing

public section

open Metric
open scoped NNReal

/-- Multiplication in a normed ring `R` is `(Bf + Bg)`-Lipschitz on the set of pairs bounded by `Bf`
and `Bg`. -/
lemma lipschitzOnWith_uncurry_mul {R : Type*} [NormedRing R] {Bf Bg : ℝ≥0} :
    LipschitzOnWith (Bf + Bg) (fun p : R × R ↦ p.1 * p.2) {p | ‖p.1‖ ≤ Bf ∧ ‖p.2‖ ≤ Bg} := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  rintro p ⟨hp1, hp2⟩ q ⟨hq1, hq2⟩
  simp only [dist_eq_norm, NNReal.coe_add]
  set D := max ‖p.1 - q.1‖ ‖p.2 - q.2‖ with hD
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (le_max_left ..)
  calc ‖p.1 * p.2 - q.1 * q.2‖
      = ‖p.1 * (p.2 - q.2) + (p.1 - q.1) * q.2‖ := by noncomm_ring
    _ ≤ ‖p.1‖ * ‖p.2 - q.2‖ + ‖p.1 - q.1‖ * ‖q.2‖ :=
        (norm_add_le ..).trans (add_le_add (norm_mul_le ..) (norm_mul_le ..))
    _ ≤ ↑Bf * D + D * ↑Bg :=
        add_le_add (mul_le_mul hp1 (le_max_right ..) (norm_nonneg _) Bf.coe_nonneg)
          (mul_le_mul (le_max_left ..) hq2 (norm_nonneg _) hD0)
    _ = (↑Bf + ↑Bg) * D := by ring

/-- In a normed ring, `‖aⁿ - bⁿ‖ ≤ n * Bⁿ⁻¹ * ‖a - b‖` whenever `‖a‖, ‖b‖ ≤ B`. -/
lemma norm_pow_sub_pow_le {R : Type*} [NormedRing R] {a b : R} {B : ℝ} (ha : ‖a‖ ≤ B)
    (hb : ‖b‖ ≤ B) : ∀ n : ℕ, ‖a ^ n - b ^ n‖ ≤ n * B ^ (n - 1) * ‖a - b‖
  | 0 => by simp
  | 1 => by simp
  | (n + 2) => by
    have hB : 0 ≤ B := (norm_nonneg a).trans ha
    have ih : ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤ (n + 1 : ℝ) * B ^ n * ‖a - b‖ := by
      simpa using norm_pow_sub_pow_le ha hb (n + 1)
    have hbn : ‖b ^ (n + 1)‖ ≤ B ^ (n + 1) := (norm_pow_le' b n.succ_pos).trans (by gcongr)
    have goal : ‖a ^ (n + 2) - b ^ (n + 2)‖ ≤ (n + 2 : ℝ) * B ^ (n + 1) * ‖a - b‖ :=
      calc ‖a ^ (n + 2) - b ^ (n + 2)‖
          = ‖a * (a ^ (n + 1) - b ^ (n + 1)) + (a - b) * b ^ (n + 1)‖ := by
            rw [show a ^ (n + 2) - b ^ (n + 2)
              = a * (a ^ (n + 1) - b ^ (n + 1)) + (a - b) * b ^ (n + 1) from by
                rw [pow_succ' a, pow_succ' b]; noncomm_ring]
        _ ≤ ‖a‖ * ‖a ^ (n + 1) - b ^ (n + 1)‖ + ‖a - b‖ * ‖b ^ (n + 1)‖ :=
            (norm_add_le ..).trans (add_le_add (norm_mul_le ..) (norm_mul_le ..))
        _ ≤ B * ((n + 1 : ℝ) * B ^ n * ‖a - b‖) + ‖a - b‖ * B ^ (n + 1) := by gcongr
        _ = (n + 2 : ℝ) * B ^ (n + 1) * ‖a - b‖ := by ring
    simpa using goal

/-- The `n`-th power map is uniformly continuous on the set of elements of norm at most `B`, with
modulus `ε ↦ ε / (n * Bⁿ⁻¹ + 1)`. -/
lemma isUniformContinuousOnWith_pow {R : Type*} [NormedRing R] (n : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    IsUniformContinuousOnWith (fun ε ↦ ε / (n * B ^ (n - 1) + 1)) (· ^ n : R → R)
      {y | ‖y‖ ≤ B} := by
  rintro ε hε a ha b hb hab
  rw [Set.mem_ofPred_eq] at ha hb
  have hden : (0 : ℝ) < n * B ^ (n - 1) + 1 := by positivity
  rw [dist_eq_norm]
  calc ‖a ^ n - b ^ n‖
      ≤ n * B ^ (n - 1) * ‖a - b‖ := norm_pow_sub_pow_le ha hb n
    _ = n * B ^ (n - 1) * dist a b := by rw [dist_eq_norm]
    _ ≤ n * B ^ (n - 1) * (ε / (n * B ^ (n - 1) + 1)) := by gcongr
    _ ≤ ε := by rw [← mul_div_assoc, div_le_iff₀ hden]; nlinarith [hε.le]
