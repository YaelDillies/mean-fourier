/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import MeanFourier.AlmostPeriod.Uniform
public import MeanFourier.InvtMean.Defs

/-!
# The von Neumann mean

This file defines the von Neumann mean.

## References

* [*Almost periodic functions in a group. I*, John von Neumann](https://doi.org/10.2307/1989792)
-/

public section

open Bornology

namespace InvtMean
variable {G 𝕜 E : Type*} [Group G] [RCLike 𝕜] [NormedAddCommGroup E] [PartialOrder E]
  [NormedSpace 𝕜 E] [NormedSpace ℝ E]

/-- The von Neumann mean -/
@[expose, simps]
noncomputable def vn : InvtMean G 𝕜 E where
  IsMeasFun f := IsUAP f
  toFun f :=
    open scoped Classical in
    if hf : IsUAP f then
      hf.isAlmostConvergent.existsUnique_const_mem_closure_convexHull.choose
    else
      0
  map_zero := by simp; grind
  map_add := by
    rintro f hf g hg
    rw [dif_pos hf, dif_pos hg, dif_pos (hf.add hg),
      (hf.add hg).isAlmostConvergent.existsUnique_const_mem_closure_convexHull.choose_eq_iff]
    sorry
  map_smul := by
    rintro f hf z
    rw [dif_pos hf, dif_pos hf.smul,
      hf.smul.isAlmostConvergent.existsUnique_const_mem_closure_convexHull.choose_eq_iff]
    sorry
  map_translate := by
    rintro f hf x
    rw [dif_pos hf, dif_pos hf.translate,
      hf.translate.isAlmostConvergent.existsUnique_const_mem_closure_convexHull.choose_eq_iff]
    sorry
  map_nonneg := by
    rintro f hf₀ hf
    rw [dif_pos hf]
    sorry

end InvtMean
