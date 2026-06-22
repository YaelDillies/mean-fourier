/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import MeanFourier.InvtMean.VonNeumann

public section

open InvtMean

variable {G E : Type*} [Group G]

section NormedAddCommGroup
variable [PartialOrder E] [NormedAddCommGroup E] [NormedSpace ℝ E] {f : G → E} {ε : ℝ}

variable (f) in
/-- A function `f` from a group `G` to a normed space `E` is almost-periodically Riemann-integrable
if for all `ε > 0` it is possible to write `f` as a pointwise convex combination of UAP
whose means are all at most `ε` apart. -/
@[expose, fun_prop] def IsAPRiemann : Prop :=
  ∀ ⦃ε⦄, 0 < ε → ∃ s : Set (G → E), (∀ g ∈ s, IsUAP g) ∧
    (∀ g ∈ s, ∀ h ∈ s, ‖vn ℝ g - vn ℝ h‖ ≤ ε) ∧ ∀ x, f x ∈ convexHull ℝ ((· x) '' s)

@[fun_prop] lemma IsUAP.isAPRiemann (hf : IsUAP f) : IsAPRiemann f :=
  fun ε hε ↦ ⟨{f}, by simp [le_of_lt, *]⟩

end NormedAddCommGroup

section Real
variable {f : G → ℝ} {ε : ℝ}

/-- A real-valued function is AP-Riemann integrable iff it is sandwiched arbitrarily well between
two UAP functions. -/
lemma isAPRiemann_iff_exists_le_ge_isUAP :
    IsAPRiemann f ↔ ∀ ⦃ε⦄, 0 < ε → ∃ g ≤ f, IsUAP g ∧ ∃ h ≥ f, IsUAP h ∧ vn ℝ h - vn ℝ g ≤ ε := by
  sorry

alias ⟨IsAPRiemann.exists_le_ge_isUAP, IsAPRiemann.of_exists_le_ge_isUAP⟩ :=
  isAPRiemann_iff_exists_le_ge_isUAP

/-- Any two means that measure an AP-Riemann integrable function `f` agree on what its mean is. -/
lemma IsAPRiemann.mean_congr {f : G → ℝ} {m m' : InvtMean G ℝ ℝ} (hf : IsAPRiemann f)
    (hfm : m.IsMeasFun f) (hfm' : m'.IsMeasFun f) : m f = m' f := by
  wlog hmf : m f ≤ m' f
  · exact (this hf hfm' hfm <| by linarith).symm
  refine hmf.antisymm <| le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨g, hgf, hg, h, hfh, hh, hgh⟩ := hf.exists_le_ge_isUAP hε
  sorry

end Real
