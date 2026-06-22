/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import MeanFourier.BohrSet.Regular
public import MeanFourier.AlmostPeriod.L2

/-!
# The averaging argument
-/

open scoped ComplexOrder Indicator Pointwise symmDiff

variable {G : Type*} [Group G] {m : InvtMean G ℂ ℂ} {A : Set G} {B : BohrSet G} {ε : ℝ}

public theorem averaging (hA : m.IsMeasSet A) (hB : B.IsRegular)
    (hBA : B.chordSet ⊆ AP_L^2(m)(𝟭_[A], ε / 8)) :
    ∃ A' ⊆ A, (1 - ε) * m 𝟭_[A] ≤ m 𝟭_[A'] ∧ ∃ c > (0 : ℝ),
      m 𝟭_[A ∆ ((c • B).chordSet * A')] ≤ ε * m 𝟭_[A] := by
  let A' := {a ∈ A | sorry}
  simp only [Set.subset_def, InvtMean.mem_l2AP_indicator_one] at hBA
  sorry
