/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.Additive.CovBySMul
public import MeanFourier.InvtMean.Defs
public import MeanFourier.UnitaryRepresentation

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
    t ∈ AP_L^2(m)(𝟭_[A], ε) ↔ m (𝟭_[t • A] - 𝟭_[A]) ≤ ε ^ 2 * m 𝟭_[A] := by
  sorry

variable (m K f) in
def IsL2APWith : Prop := ∀ ε > 0, CovBySMul G (K ε) .univ AP_L^2(m)(f, ε)

end InvtMean

section IsAP
variable {G : Type*} [Group G] {f : G → ℂ}

variable (f) in
@[expose]
def IsAP : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : Finset G, ∀ x : G, ∃ t ∈ T, ∀ y, ‖f (x⁻¹ * y) - f (t⁻¹ * y)‖ ≤ ε

open scoped InnerProductSpace in
theorem UnitaryRepresentation.isAP_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : UnitaryRepresentation ℂ G E) (v w : E) :
    IsAP fun x ↦ ⟪ρ x v, w⟫_ℂ := by
  classical
  intro ε hε
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have horb : TotallyBounded (Set.range fun t : G ↦ ρ t w) := by
    refine (isCompact_closedBall (0 : E) ‖w‖).totallyBounded.subset ?_
    rintro - ⟨t, rfl⟩
    simp
  set ε' : ℝ := ε / (‖v‖ + 1) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨c, hcsub, hcfin, hccover⟩ := totallyBounded_iff_subset.1 horb _
    (Metric.dist_mem_uniformity hε'pos)
  have hch : ∀ y ∈ c, ∃ t : G, ρ t w = y := fun y hy ↦ hcsub hy
  choose! tc htc using hch
  refine ⟨hcfin.toFinset.image tc, fun x ↦ ?_⟩
  have hx : ρ x w ∈ ⋃ y ∈ c, {z | (z, y) ∈ {p : E × E | dist p.1 p.2 < ε'}} :=
    hccover ⟨x, rfl⟩
  rw [Set.mem_iUnion₂] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  refine ⟨tc y, Finset.mem_image_of_mem _ (hcfin.mem_toFinset.2 hy), fun z ↦ ?_⟩
  have hkey : ∀ s : G, ⟪ρ (s⁻¹ * z) v, w⟫_ℂ = ⟪ρ z v, ρ s w⟫_ℂ := by
    intro s
    have h1 : ρ (s⁻¹ * z) v = (ρ s).symm (ρ z v) := by simp
    rw [h1]
    calc ⟪(ρ s).symm (ρ z v), w⟫_ℂ
        = ⟪ρ s ((ρ s).symm (ρ z v)), ρ s w⟫_ℂ := ((ρ s).inner_map_map _ _).symm
      _ = ⟪ρ z v, ρ s w⟫_ℂ := by simp
  beta_reduce
  rw [hkey x, hkey (tc y), ← inner_sub_right]
  calc ‖⟪ρ z v, ρ x w - ρ (tc y) w⟫_ℂ‖
      ≤ ‖ρ z v‖ * ‖ρ x w - ρ (tc y) w‖ := norm_inner_le_norm _ _
    _ = ‖v‖ * ‖ρ x w - ρ (tc y) w‖ := by simp
    _ ≤ ‖v‖ * ε' := by
        gcongr
        rw [htc y hy, ← dist_eq_norm]
        grind
    _ ≤ ε := by
        rw [hε', mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        grind

end IsAP
