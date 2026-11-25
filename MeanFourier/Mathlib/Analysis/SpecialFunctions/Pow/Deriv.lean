module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import MeanFourier.Mathlib.Topology.MetricSpace.Pseudo.Defs

public section

open Metric Real

/-- The map `x ↦ x ^ r` is `|r| * (c ^ (r - 1) ⊔ B ^ (r - 1))`-Lipschitz on `[c, B]` (with
`0 < c`). -/
lemma lipschitzOnWith_rpow (r : ℝ) {c B : ℝ} (hc : 0 < c) :
    LipschitzOnWith (|r| * (c ^ (r - 1) ⊔ B ^ (r - 1))).toNNReal (· ^ r : ℝ → ℝ) (Set.Icc c B) := by
  set C := |r| * (c ^ (r - 1) ⊔ B ^ (r - 1)) with hCdef
  have hcp : (0 : ℝ) < c ^ (r - 1) ⊔ B ^ (r - 1) := (rpow_pos_of_pos hc _).trans_le le_sup_left
  have hC0 : 0 ≤ C := by rw [hCdef]; exact mul_nonneg (abs_nonneg _) hcp.le
  have hderiv : ∀ x ∈ Set.Icc c B, HasDerivWithinAt (· ^ r) (r * x ^ (r - 1)) (Set.Icc c B) x :=
    fun x hx ↦ (hasDerivAt_rpow_const (Or.inl (hc.trans_le hx.1).ne')).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Icc c B, ‖r * x ^ (r - 1)‖ ≤ C := by
    rintro x ⟨hx1, hx2⟩
    rw [hCdef, norm_mul, norm_eq_abs, norm_eq_abs,
      abs_of_pos (rpow_pos_of_pos (hc.trans_le hx1) _)]
    gcongr
    rcases le_or_gt 1 r with hr | hr
    · exact le_sup_of_le_right (rpow_le_rpow (hc.trans_le hx1).le hx2 (by linarith))
    · exact le_sup_of_le_left (rpow_le_rpow_of_nonpos hc hx1 (by linarith))
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro a ha b hb
  simp only [Real.coe_toNNReal _ hC0, dist_eq_norm]
  exact (convex_Icc c B).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hb ha

open Complex in
/-- The complex power `z ↦ z ^ w` is `‖w‖ * (c ^ (w.re - 1) ⊔ B ^ (w.re - 1)) * exp (π * |w.im|)`-
Lipschitz on any convex subset `S` of the slit plane whose elements have norm in `[c, B]`
(with `0 < c`). -/
lemma lipschitzOnWith_cpow (w : ℂ) {c B : ℝ} {S : Set ℂ} (hc : 0 < c)
    (hS : Convex ℝ S) (hSslit : S ⊆ slitPlane) (hSc : ∀ z ∈ S, c ≤ ‖z‖)
    (hSB : ∀ z ∈ S, ‖z‖ ≤ B) :
    LipschitzOnWith (‖w‖ * (c ^ (w.re - 1) ⊔ B ^ (w.re - 1)) * .exp (π * |w.im|)).toNNReal
      (· ^ w : ℂ → ℂ) S := by
  set C := ‖w‖ * (c ^ (w.re - 1) ⊔ B ^ (w.re - 1)) * .exp (π * |w.im|) with hCdef
  have hsup : (0 : ℝ) < c ^ (w.re - 1) ⊔ B ^ (w.re - 1) :=
    (rpow_pos_of_pos hc _).trans_le le_sup_left
  have hC0 : 0 ≤ C := by positivity
  have hderiv : ∀ z ∈ S, HasDerivWithinAt (· ^ w) (w * z ^ (w - 1)) S z :=
    fun z hz ↦ (Complex.hasStrictDerivAt_cpow_const (hSslit hz)).hasDerivAt.hasDerivWithinAt
  have hbound : ∀ z ∈ S, ‖w * z ^ (w - 1)‖ ≤ C := by
    intro z hz
    have hz0 : 0 < ‖z‖ := hc.trans_le (hSc z hz)
    rw [hCdef, norm_mul, mul_assoc]
    gcongr
    calc ‖z ^ (w - 1)‖
        ≤ ‖z‖ ^ (w - 1).re / .exp (arg z * (w - 1).im) := norm_cpow_le ..
      _ = ‖z‖ ^ (w.re - 1) * (.exp (arg z * w.im))⁻¹ := by
          rw [div_eq_mul_inv]; simp [Complex.sub_re, Complex.sub_im]
      _ ≤ (c ^ (w.re - 1) ⊔ B ^ (w.re - 1)) * .exp (π * |w.im|) := by
          gcongr ?_ * ?_
          · rcases le_or_gt 0 (w.re - 1) with hp | hp
            · exact le_sup_of_le_right (rpow_le_rpow hz0.le (hSB z hz) hp)
            · exact le_sup_of_le_left (rpow_le_rpow_of_nonpos hc (hSc z hz) hp.le)
          · grw [← Real.exp_neg, exp_le_exp, neg_le_abs, abs_mul, Complex.abs_arg_le_pi]
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro a ha b hb
  simp only [Real.coe_toNNReal _ hC0, dist_eq_norm]
  exact hS.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hb ha
