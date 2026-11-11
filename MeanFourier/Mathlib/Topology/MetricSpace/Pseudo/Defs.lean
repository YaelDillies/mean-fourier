module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

public section

open scoped NNReal

namespace Metric
variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {δ : ℝ → ℝ} {f : X → Y}

attribute [fun_prop] UniformContinuous UniformContinuousOn

variable (δ f) in
/-- A function between metric spaces is uniformly continuous with modulus of continuity `δ : ℝ → ℝ`
if `dist x y ≤ δ(ε) → dist (f x) (f y) ≤ ε` for all `x`, `y`. -/
@[expose, fun_prop]
def IsUniformContinuousWith : Prop :=
  ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ ⦃x y : X⦄, dist x y ≤ δ ε → dist (f x) (f y) ≤ ε

@[fun_prop]
lemma IsUniformContinuousWith.uniformContinuous (hδ : ∀ ε > 0, 0 < δ ε)
    (hf : IsUniformContinuousWith δ f) : UniformContinuous f :=
  uniformContinuous_iff_le.2 fun ε hε ↦ ⟨δ ε, hδ _ hε, hf hε⟩

lemma uniformContinuous_iff_exists_isUniformContinuousWith :
    UniformContinuous f ↔ ∃ δ : ℝ → ℝ, (∀ ε > 0, 0 < δ ε) ∧ IsUniformContinuousWith δ f where
  mp hf := by rw [uniformContinuous_iff_le] at hf; choose! δ hδ hf using hf; exact ⟨δ, hδ, hf⟩
  mpr := by rintro ⟨δ, hδ, hf⟩; fun_prop

/-- A `K`-Lipschitz function is uniformly continuous with modulus of continuity `ε ↦ ε / K`. -/
@[fun_prop]
lemma _root_.LipschitzWith.isUniformContinuousWith {K : ℝ≥0} (hf : LipschitzWith K f) :
    IsUniformContinuousWith (fun ε ↦ ε / K) f := by
  rintro ε hε x y hxy
  grw [hf.dist_le_mul]
  obtain rfl | hK := eq_or_ne K 0
  · simp [zero_mul, hε.le]
  · grw [hxy]
    field_simp
    rfl

variable (δ f) in
/-- A function is uniformly continuous on a set `S` with modulus of continuity `δ : ℝ → ℝ` if
`dist x y ≤ δ(ε) → dist (f x) (f y) ≤ ε` for all `x`, `y` in `S`.

This is the "on a set" version of `IsUniformContinuousWith`, and a quantitative version of
`UniformContinuousOn`. It is implied by `LipschitzOnWith`. -/
@[expose, fun_prop]
def IsUniformContinuousOnWith (S : Set X) : Prop :=
  ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → dist x y ≤ δ ε → dist (f x) (f y) ≤ ε

@[simp] lemma isUniformContinuousOnWith_univ :
    IsUniformContinuousOnWith δ f .univ ↔ IsUniformContinuousWith δ f := by
  simp [IsUniformContinuousOnWith, IsUniformContinuousWith]

/-- A uniformly continuous function is uniformly continuous on every set. -/
@[fun_prop]
lemma IsUniformContinuousWith.isUniformContinuousOnWith (hf : IsUniformContinuousWith δ f)
    (S : Set X) : IsUniformContinuousOnWith δ f S := fun _ hε _ _ _ _ hxy ↦ hf hε hxy

@[fun_prop]
lemma IsUniformContinuousOnWith.uniformContinuousOn {S : Set X} (hδ : ∀ ε > 0, 0 < δ ε)
    (hf : IsUniformContinuousOnWith δ f S) : UniformContinuousOn f S :=
  uniformContinuousOn_iff_le.2 fun ε hε ↦ ⟨δ ε, hδ _ hε, hf hε⟩

lemma uniformContinuousOn_iff_exists_isUniformContinuousOnWith {S : Set X} :
    UniformContinuousOn f S ↔ ∃ δ, (∀ ε > 0, 0 < δ ε) ∧ IsUniformContinuousOnWith δ f S where
  mp hf := by rw [uniformContinuousOn_iff_le] at hf; choose! δ hδ hf using hf; exact ⟨δ, hδ, hf⟩
  mpr := by rintro ⟨δ, hδ, hf⟩; fun_prop

/-- A function that is `K`-Lipschitz on a set `S` is uniformly continuous on `S` with modulus of
continuity `ε ↦ ε / K`. -/
@[fun_prop]
lemma _root_.LipschitzOnWith.isUniformContinuousOnWith {K : ℝ≥0} {S : Set X}
    (hf : LipschitzOnWith K f S) : IsUniformContinuousOnWith (fun ε ↦ ε / K) f S := by
  rintro ε hε x hx y hy hxy
  grw [hf.dist_le_mul _ hx _ hy]
  obtain rfl | hK := eq_or_ne K 0
  · simp [zero_mul, hε.le]
  · grw [hxy]
    field_simp
    rfl

/-- If `f` is uniformly continuous on `S` with modulus `ε ↦ ε / K` for some `0 < K`,
then `f` is `K`-Lipschitz on `S`. -/
lemma IsUniformContinuousOnWith.lipschitzOnWith {K : ℝ≥0} {S : Set X} (hK : 0 < K)
    (hf : IsUniformContinuousOnWith (fun ε ↦ ε / K) f S) : LipschitzOnWith K f S := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  refine fun x hx y hy ↦ le_of_forall_gt_imp_ge_of_dense fun a ha ↦ hf (ha.trans_le' ?_) hx hy ?_
  · positivity
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [ha]

/-- A function is `K`-Lipschitz on `S` iff it is uniformly continuous on `S` with modulus
`ε ↦ ε / K`, provided `0 < K`. -/
lemma lipschitzOnWith_iff_isUniformContinuousOnWith {K : ℝ≥0} {S : Set X} (hK : 0 < K) :
    LipschitzOnWith K f S ↔ IsUniformContinuousOnWith (fun ε ↦ ε / K) f S :=
  ⟨LipschitzOnWith.isUniformContinuousOnWith, IsUniformContinuousOnWith.lipschitzOnWith hK⟩

/-- Conversely, if `f` is uniformly continuous with modulus `ε ↦ ε / K` for some `0 < K`,
then `f` is `K`-Lipschitz. -/
lemma IsUniformContinuousWith.lipschitzWith {K : ℝ≥0} (hK : 0 < K)
    (hf : IsUniformContinuousWith (fun ε ↦ ε / K) f) : LipschitzWith K f :=
  lipschitzOnWith_univ.1 ((isUniformContinuousOnWith_univ.2 hf).lipschitzOnWith hK)

/-- A function is `K`-Lipschitz iff it is uniformly continuous with modulus `ε ↦ ε / K`, provided
`0 < K`. -/
lemma lipschitzWith_iff_isUniformContinuousWith {K : ℝ≥0} (hK : 0 < K) :
    LipschitzWith K f ↔ IsUniformContinuousWith (fun ε ↦ ε / K) f :=
  ⟨LipschitzWith.isUniformContinuousWith, IsUniformContinuousWith.lipschitzWith hK⟩

end Metric
