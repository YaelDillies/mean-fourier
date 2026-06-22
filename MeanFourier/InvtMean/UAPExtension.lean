/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import MeanFourier.InvtMean.VonNeumann

/-!
# Extending invariant means to UAP functions

This file proves that every invariant mean extends uniquely to an invariant mean for which
uniformly almost-periodic functions are measurable.
-/

public section

open scoped ComplexOrder

namespace InvtMean
variable {G : Type*} [Group G] {m : InvtMean G ℂ ℂ}

variable (m) in
/-- The unique extension of an invariant mean to uniformly almost-periodic functions. -/
noncomputable def uapExtension : InvtMean G ℂ ℂ where
  IsMeasFun f := ∃ g, m.IsMeasFun g ∧ ∃ h, IsUAP h ∧ g + h = f
  isMeasFun_const z := ⟨0, by simp, fun _ ↦ z, by simp⟩
  isMeasFun_add := by
    rintro _ ⟨f, hf, g, hg, rfl⟩ _ ⟨h, hh, i, hi, rfl⟩
    exact ⟨f + h, hf.add hh, g + i, hg.add hi, add_add_add_comm ..⟩
  isMeasFun_smul := by
    rintro z _ ⟨f, hf, g, hg, rfl⟩
    exact ⟨z • f, hf.smul, z • g, hg.smul, by simp [smul_add]⟩
  isMeasFun_translate := by
    rintro x _ ⟨f, hf, g, hg, rfl⟩
    exact ⟨τ_[x] f, hf.translate, τ_[x] g, hg.translate, by simp only [Function.translate_add_fun]⟩
  isBddFun_of_isMeasFun := by rintro _ ⟨f, hf, g, hg, rfl⟩; exact hf.isBddFun.add hg.isBddFun
  toFun f :=
    have : Decidable (∃ g, m.IsMeasFun g ∧ ∃ h, IsUAP h ∧ g + h = f) := Classical.dec _
    if hf : ∃ g, m.IsMeasFun g ∧ ∃ h, IsUAP h ∧ g + h = f then
      m.toFun hf.choose + vn ℝ hf.choose_spec.2.choose
    else
      0
  map_zero := by
    simp only [add_eq_zero_iff_eq_neg, ↓existsAndEq, isMeasFun_neg, and_true, vn_apply,
      dite_eq_right_iff, forall_exists_index, forall_and_index]
    rintro f hf hf'
    sorry
  map_add := by
    sorry
  map_smul := by
    sorry
  map_translate := by
    sorry
  map_nonneg := by
    sorry

end InvtMean
