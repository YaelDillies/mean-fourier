/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.Additive.CovBySMul
public import MeanFourier.InvtMean.Defs

/-!
# L^2(m)
-/

public section

open scoped Indicator Pointwise

namespace InvtMean
variable {G : Type*} [Group G] {m : InvtMean G} {f : G → ℂ} {A : Set G} {t : G} {K : ℝ → ℝ} {ε : ℝ}

variable (m f ε) in
def l2AP : Set G := {t | m.l2Norm ((fun g ↦ f (t⁻¹ * g)) - f) ≤ ε * m.l2Norm f}

notation3 "AP_L^2(" m ")(" f ", " ε ")" => l2AP m f ε

@[simp]
lemma mem_l2AP : t ∈ AP_L^2(m)(f, ε) ↔ m.l2Norm ((fun g ↦ f (t⁻¹ * g)) - f) ≤ ε * m.l2Norm f := .rfl

@[simp high]
lemma mem_l2AP_indicator_one :
    t ∈ AP_L^2(m)(𝟭_[A], ε) ↔ m (|𝟭_[t • A] - 𝟭_[A]|) ≤ ε ^ 2 * m 𝟭_[A] := by
  sorry

variable (m K f) in
def IsL2APWith : Prop := ∀ ε > 0, CovBySMul G (K ε) .univ AP_L^2(m)(f, ε)

end InvtMean
