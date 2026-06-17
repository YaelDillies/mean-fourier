/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import MeanFourier.AlmostConvergent
public import MeanFourier.UnitaryRepresentation
public import MeanFourier.Mathlib.Analysis.Normed.Group.Bounded
public import MeanFourier.Mathlib.Combinatorics.Additive.CovBySMul
public import MeanFourier.Mathlib.Data.ENat.Basic
public import MeanFourier.Mathlib.Data.EReal.Basic
public import MeanFourier.Mathlib.Data.Real.ENatENNReal
public import MeanFourier.Mathlib.Topology.Bornology.Basic
public import MeanFourier.Mathlib.Topology.MetricSpace.CoveringNumbers
public import MeanFourier.Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Uniformly almost-periodic functions

This files defines uniformly almost-periodic functions in a group following von Neumann.

## References

* [*Almost periodic functions in a group. I*, John von Neumann](https://doi.org/10.2307/1989792)
-/

public section

open Bornology Metric
open scoped Pointwise

variable {𝕜 G R E : Type*} [RCLike 𝕜] [Group G] {K L : ℝ → ℝ} {a x t : G} {c : 𝕜}

section NormedAddCommGroup
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f g : G → E} {z : E} {ε : ℝ}

variable (f ε) in
/-- The uniform `ε`-almost periods of a function `f` from a group `G` to a normed space `E` are
those elements of the group that move `f` by at most `ε` in L^∞ norm. -/
def uniformAP : Set G := {t | ∀ x, ‖f (t⁻¹ * x) - f x‖ ≤ ε}

@[inherit_doc uniformAP] notation3 "AP∞("f ", " ε ")" => uniformAP f ε

@[simp] lemma mem_uniformAP : t ∈ AP∞(f, ε) ↔ ∀ x, ‖f (t⁻¹ * x) - f x‖ ≤ ε := .rfl

@[simp]
lemma uniformAP_inv : AP∞(f, ε)⁻¹ = AP∞(f, ε) := by
  ext t
  exact (Equiv.mulLeft t).forall_congr (by simp [norm_sub_rev])

lemma inv_mem_uniformAP (ht : t ∈ AP∞(f, ε)) : t⁻¹ ∈ AP∞(f, ε) := by
  rw [← uniformAP_inv]; exact Set.inv_mem_inv.2 ht

@[to_fun (attr := simp) uniformAP_fun_const]
lemma uniformAP_const (hε : 0 ≤ ε) : AP∞(Function.const G z, ε) = .univ := by simp [uniformAP, hε]

@[to_fun (attr := simp) uniformAP_fun_smul]
lemma uniformAP_smul (hc : c ≠ 0) : AP∞(c • f, ε) = AP∞(f, ε / ‖c‖) := by
  ext t; simp [← smul_sub, norm_smul, le_div_iff₀' (norm_pos_iff.2 hc)]

/-- The almost periods of `f ∘ φ` are the preimage under a group isomorphism `φ` of those of `f`. -/
@[simp]
lemma uniformAP_comp_mulEquiv {H : Type*} [Group H] (φ : H ≃* G) :
    AP∞(f ∘ φ, ε) = φ ⁻¹' AP∞(f, ε) := by
  ext; simp [φ.surjective.forall]

/-- The almost periods are unchanged by right translation of the argument. -/
@[simp] lemma uniformAP_comp_mul_right (a : G) : AP∞(fun x ↦ f (x * a), ε) = AP∞(f, ε) := by
  ext t; exact (Equiv.mulRight a).forall_congr <| by simp [mul_assoc]

@[simp]
lemma uniformAP_translate : AP∞(τ_[x] f, ε) = AP∞(f, ε) := by
  sorry
  -- ext t; exact (Equiv.mulRight x).symm.forall_congr <| by simp

variable (K f) in
/-- For a "modulus of almost-periodicity" `K : ℝ → ℝ`,a function is uniformly `K`-almost-periodic
if its uniform `ε`-almost periods are `K_ε`-syndetic for all `ε > 0`.

This is a quantitative version of `IsUAP`. -/
@[expose, fun_prop] def IsUAPWith : Prop := ∀ ⦃ε⦄, 0 < ε → CovBySMul G (K ε) .univ AP∞(f, ε)

@[to_fun (attr := simp, fun_prop)]
protected lemma IsUAPWith.const : IsUAPWith 1 (Function.const G z) := by
  simp +contextual [IsUAPWith, le_of_lt]

@[simp, fun_prop]
protected lemma IsUAPWith.zero : IsUAPWith 1 (0 : G → E) := .const

lemma mul_mem_uniformAP {a b : G} {δ : ℝ} (ha : a ∈ AP∞(f, ε)) (hb : b ∈ AP∞(f, δ)) :
    a * b ∈ AP∞(f, ε + δ) := by
  rw [mem_uniformAP] at ha hb
  intro x
  have : f ((a * b)⁻¹ * x) - f x
      = (f (b⁻¹ * (a⁻¹ * x)) - f (a⁻¹ * x)) + (f (a⁻¹ * x) - f x) := by grind [mul_inv_rev]
  grind [norm_add_le]

lemma uniformAP_mul_uniformAP_subset {δ : ℝ} : AP∞(f, ε) * AP∞(f, δ) ⊆ AP∞(f, ε + δ) := by
  intro _ ⟨_, _, _, _, _⟩
  grind [mul_mem_uniformAP]

lemma uniformAP_pow_subset : ∀ n : ℕ, AP∞(f, ε) ^ n ⊆ AP∞(f, n * ε)
  | 0 => by simp [mem_uniformAP]
  | n + 1 => by
    grw [pow_succ, uniformAP_pow_subset, uniformAP_mul_uniformAP_subset]
    grind [uniformAP]

lemma inter_subset_uniformAP_add {δ : ℝ} :
    AP∞(f, ε) ∩ AP∞(g, δ) ⊆ AP∞(f + g, ε + δ) := by
  intro t ht
  obtain ⟨htf, htg⟩ := ht
  intro x
  have : f (t⁻¹ * x) + g (t⁻¹ * x) - (f x + g x)
      = (f (t⁻¹ * x) - f x) + (g (t⁻¹ * x) - g x) := by grind
  grind [Pi.add_apply, norm_add_le, htf x, htg x]

protected lemma IsUAPWith.add (hf : IsUAPWith K f) (hg : IsUAPWith L g) :
    IsUAPWith (fun ε ↦ K (ε / 4) * L (ε / 4)) (f + g) := by
  rintro ε hε
  replace hε : (0 : ℝ) < ε / 4 := by linarith
  refine ((hf hε).inter (hg hε)).subset_right ?_
  grw [uniformAP_inv, uniformAP_inv, uniformAP_mul_uniformAP_subset, uniformAP_mul_uniformAP_subset,
    inter_subset_uniformAP_add]
  grind

@[to_fun]
protected lemma IsUAPWith.smul (hf : IsUAPWith K f) (hc : c ≠ 0) :
    IsUAPWith (fun ε ↦ K <| ε / ‖c‖) (c • f) := by
  rintro ε hε
  simp only [ne_eq, hc, not_false_eq_true, uniformAP_smul]
  exact hf <| by positivity

@[fun_prop]
protected lemma IsUAPWith.translate (hf : IsUAPWith K f) : IsUAPWith K (τ_[t] f) := by
  simpa [IsUAPWith] using hf

protected lemma IsUAPWith.comp_mul_right (hf : IsUAPWith K f) :
    IsUAPWith K (fun x ↦ f (x * a)) := by simpa [IsUAPWith] using hf

variable (f) in
/-- A function is uniformly almost periodic if its uniform `ε`-almost periods are syndetic for all
`ε > 0`. -/
@[expose, fun_prop] def IsUAP : Prop := ∀ ⦃ε⦄, 0 < ε → ∃ K, CovBySMul G K .univ AP∞(f, ε)

@[fun_prop] lemma IsUAPWith.isUAP (hf : IsUAPWith K f) : IsUAP f := fun ε hε ↦ ⟨K ε, hf hε⟩

lemma isUAP_iff_exists_isUAPWith : IsUAP f ↔ ∃ K, IsUAPWith K f where
  mp hf := by choose! K hf using hf; exact ⟨K, hf⟩
  mpr := by rintro ⟨K, hf⟩; exact hf.isUAP

alias ⟨IsUAP.exists_isUAPWith, _⟩ := isUAP_iff_exists_isUAPWith

@[to_fun (attr := simp, fun_prop)]
protected lemma IsUAP.const : IsUAP (Function.const G z) := fun ε hε ↦ ⟨1, by simp [hε.le]⟩

@[simp, fun_prop] protected lemma IsUAP.zero : IsUAP (0 : G → E) := .const

@[to_fun (attr := fun_prop)]
protected lemma IsUAP.add (hf : IsUAP f) (hg : IsUAP g) : IsUAP (f + g) := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith
  obtain ⟨L, hg⟩ := hg.exists_isUAPWith
  exact (hf.add hg).isUAP

@[to_fun (attr := fun_prop)]
protected lemma IsUAP.smul (hf : IsUAP f) : IsUAP (c • f) := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  · obtain ⟨K, hf⟩ := hf.exists_isUAPWith
    exact (hf.smul hc).isUAP

/-- Almost periodicity is preserved by precomposition with a group isomorphism. -/
protected lemma IsUAP.comp_mulEquiv {H : Type*} [Group H] (φ : H ≃* G) (hf : IsUAP f) :
    IsUAP (f ∘ φ) := by
  classical
  intro ε hε
  obtain ⟨K, F, hFK, hcov⟩ := hf hε
  refine ⟨K, F.image φ.symm, by grw [Finset.card_image_le, hFK], fun h _ ↦ ?_⟩
  obtain ⟨a, ha, s, hs, hgs⟩ := Set.mem_smul.1 (hcov (Set.mem_univ (φ h)))
  rw [smul_eq_mul] at hgs
  rw [uniformAP_comp_mulEquiv]
  exact ⟨φ.symm a, Finset.mem_image_of_mem _  ha, φ.symm s, by simpa using hs, by
    simp [← map_mul, hgs]⟩

protected lemma IsUAP.comp_mul_right (hf : IsUAP f) : IsUAP (fun x ↦ f (x * a)) := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith; exact hf.comp_mul_right.isUAP

@[fun_prop]
protected lemma IsUAP.translate (hf : IsUAP f) : IsUAP (τ_[x] f) := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith; exact hf.translate.isUAP

@[fun_prop]
protected lemma IsUAP.isBddFun (hf : IsUAP f) : IsBddFun f := by
  -- At `ε = 1`, the almost periods are syndetic: `univ ⊆ F • AP∞(f, 1)` for some finite `F`.
  obtain ⟨-, F, -, hsub⟩ := hf zero_lt_one
  -- Hence `range f` lies in the finite union of unit balls around the values `f g⁻¹`, `g ∈ F`.
  refine ((isBounded_biUnion F.finite_toSet).2 fun g _ ↦
    isBounded_closedBall (x := f g⁻¹) (r := 1)).subset ?_
  rintro _ ⟨y, rfl⟩
  obtain ⟨g, hg, t, ht, hgt⟩ := Set.mem_smul.1 (hsub (Set.mem_univ y⁻¹))
  rw [smul_eq_mul] at hgt
  -- `y = t⁻¹ * g⁻¹`, and `t` is an `ε`-almost period, so `‖f y - f g⁻¹‖ ≤ 1`.
  have hy : t⁻¹ * g⁻¹ = y := by rw [← mul_inv_rev, hgt, inv_inv]
  refine Set.mem_biUnion hg ?_
  simpa [Metric.mem_closedBall, dist_eq_norm, hy] using ht g⁻¹

section MetricSpace
variable [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] {δ : ℝ → ℝ}

lemma ball_one_subset_uniformAP_of_isUniformContinuousWith (hf : IsUniformContinuousWith δ f)
    (hε : 0 < ε) : ball 1 (δ ε) ⊆ AP∞(f, ε) := by
  rintro t ht x
  simp only [← dist_eq_norm, mem_ball'] at ht ⊢
  refine hf hε ?_
  convert! ht.le using 1
  rw [← dist_mul_right _ _ x⁻¹, mul_inv_cancel_right, mul_inv_cancel, ← dist_mul_right _ _ t]
  simp

variable [CompactSpace G]

@[fun_prop]
protected lemma Metric.IsUniformContinuousWith.isUAPWith (hδ : ∀ ε > 0, 0 < δ ε)
    (hf : IsUniformContinuousWith δ f) :
    IsUAPWith (fun ε ↦ (coveringNumber (δ ε).toNNReal (.univ : Set G)).toNat) f := by
  rintro ε hε
  grw [← ball_one_subset_uniformAP_of_isUniformContinuousWith hf hε]
  simpa using isCompact_univ.totallyBounded.coveringNumber_ne_top <| by simp [*]

@[fun_prop]
protected lemma UniformContinuous.isUAP (hf : UniformContinuous f) : IsUAP f := by
  obtain ⟨δ, hδ, hf⟩ := uniformContinuous_iff_exists_isUniformContinuousWith.1 hf
  exact (hf.isUAPWith hδ).isUAP

@[fun_prop]
protected lemma Continuous.isUAP (hf : Continuous f) : IsUAP f :=
  (CompactSpace.uniformContinuous_of_continuous hf).isUAP

end MetricSpace

@[fun_prop]
protected lemma IsUAP.isAlmostConvergent [NormedSpace ℝ E] (hf : IsUAP f) :
    IsAlmostConvergent f := by
  sorry

section Star
variable [StarAddMonoid E] [NormedStarGroup E]

/-- The almost periods are unchanged by applying an isometric `star` pointwise. -/
@[simp] lemma uniformAP_star : AP∞(fun x ↦ star (f x), ε) = AP∞(f, ε) := by
  ext t; simp only [mem_uniformAP, ← star_sub, norm_star]

@[fun_prop]
protected lemma IsUAPWith.star (hf : IsUAPWith K f) : IsUAPWith K (fun x ↦ star (f x)) := by
  simpa only [IsUAPWith, uniformAP_star] using hf

@[fun_prop]
protected lemma IsUAP.star (hf : IsUAP f) : IsUAP (fun x ↦ star (f x)) := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith; exact hf.star.isUAP

end Star

end NormedAddCommGroup

section NormedRing
variable [NormedRing R] {f g : G → R} {ε : ℝ}

/-- If `t` is an `ε`-almost period of a `Bf`-bounded `f` and a `δ`-almost period of a `Bg`-bounded
`g`, then it is a `(Bg ε + Bf δ)`-almost period of the product `f * g`. -/
lemma inter_subset_uniformAP_mul {Bf Bg δ : ℝ} (hfb : ∀ x, ‖f x‖ ≤ Bf) (hgb : ∀ x, ‖g x‖ ≤ Bg) :
    AP∞(f, ε) ∩ AP∞(g, δ) ⊆ AP∞(f * g, Bg * ε + Bf * δ) := by
  rintro t ⟨htf, htg⟩ x
  have : 0 ≤ Bf := by grw [← hfb 1, ← norm_nonneg]
  have : 0 ≤ ε := by grw [← htf 1, ← norm_nonneg]
  calc ‖(f * g) (t⁻¹ * x) - (f * g) x‖
      = ‖f (t⁻¹ * x) * (g (t⁻¹ * x) - g x) + (f (t⁻¹ * x) - f x) * g x‖ := by
        simp only [Pi.mul_apply]; noncomm_ring
    _ ≤ Bf * δ + ε * Bg := by grw [norm_add_le, norm_mul_le, norm_mul_le, hfb, htg x, htf x, hgb x]
    _ = Bg * ε + Bf * δ := by ring

/-- Quantitative form: the pointwise product of two uniformly almost periodic functions is uniformly
almost periodic, with an explicit modulus depending on bounds `Bf`, `Bg` for `f`, `g`. -/
protected lemma IsUAPWith.mul {Bf Bg : ℝ} (hfb : ∀ x, ‖f x‖ ≤ Bf) (hgb : ∀ x, ‖g x‖ ≤ Bg)
    (hf : IsUAPWith K f) (hg : IsUAPWith L g) :
    IsUAPWith (fun ε ↦ K (ε / (4 * (Bf + Bg + 1))) * L (ε / (4 * (Bf + Bg + 1)))) (f * g) := by
  have hBf : 0 ≤ Bf := by grw [← hfb 1, ← norm_nonneg]
  have hBg : 0 ≤ Bg := by grw [← hgb 1, ← norm_nonneg]
  have hden : (0 : ℝ) < 4 * (Bf + Bg + 1) := by linarith
  rintro ε hε
  set δ := ε / (4 * (Bf + Bg + 1)) with hδ_def
  refine ((hf (ε := δ) (by positivity)).inter (hg (ε := δ) (by positivity))).subset_right ?_
  grw [uniformAP_inv, uniformAP_inv, uniformAP_mul_uniformAP_subset, uniformAP_mul_uniformAP_subset,
    inter_subset_uniformAP_mul hfb hgb]
  intro t ht x
  have hge : Bg * (δ + δ) + Bf * (δ + δ) = 2 * (Bf + Bg) * ε / (4 * (Bf + Bg + 1)) := by ring
  grw [ht x, hge]
  field_simp
  nlinarith [hBf, hBg, hε]

@[fun_prop]
protected lemma IsUAP.mul (hf : IsUAP f) (hg : IsUAP g) : IsUAP (f * g) := by
  obtain ⟨Bf, hBf⟩ := hf.isBddFun.exists_forall_norm_le
  obtain ⟨Bg, hBg⟩ := hg.isBddFun.exists_forall_norm_le
  obtain ⟨K, hf'⟩ := hf.exists_isUAPWith
  obtain ⟨L, hg'⟩ := hg.exists_isUAPWith
  exact (hf'.mul hBf hBg hg').isUAP

end NormedRing

open scoped Pointwise InnerProductSpace in
theorem UnitaryRepresentation.isUAP_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : UnitaryRepresentation ℂ G E) (v w : E) :
    IsUAP fun x ↦ ⟪ρ x v, w⟫_ℂ := by
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
  set F : Finset G := hcfin.toFinset.image tc
  refine ⟨#F, F, le_rfl, ?_⟩
  rintro x -
  have hx : ρ x w ∈ ⋃ y ∈ c, {z | (z, y) ∈ {p : E × E | dist p.1 p.2 < ε'}} :=
    hccover ⟨x, rfl⟩
  rw [Set.mem_iUnion₂] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  refine ⟨tc y, Finset.mem_image_of_mem _ (hcfin.mem_toFinset.2 hy), (tc y)⁻¹ * x, ?_, ?_⟩
  · rw [mem_uniformAP]
    intro z
    have hkey : ∀ s : G, ⟪ρ (s⁻¹ * z) v, w⟫_ℂ = ⟪ρ z v, ρ s w⟫_ℂ := by
      intro s
      have h1 : ρ (s⁻¹ * z) v = (ρ s).symm (ρ z v) := by simp
      rw [h1]
      calc ⟪(ρ s).symm (ρ z v), w⟫_ℂ
          = ⟪ρ s ((ρ s).symm (ρ z v)), ρ s w⟫_ℂ := ((ρ s).inner_map_map _ _).symm
        _ = ⟪ρ z v, ρ s w⟫_ℂ := by simp
    have h1 : ((tc y)⁻¹ * x)⁻¹ * z = x⁻¹ * (tc y * z) := by group
    have h2 : z = (tc y)⁻¹ * (tc y * z) := by group
    rw [h1, h2, hkey x, hkey (tc y), ← inner_sub_right]
    calc ‖⟪ρ (tc y * z) v, ρ x w - ρ (tc y) w⟫_ℂ‖
        ≤ ‖ρ (tc y * z) v‖ * ‖ρ x w - ρ (tc y) w‖ := norm_inner_le_norm _ _
      _ = ‖v‖ * ‖ρ x w - ρ (tc y) w‖ := by simp
      _ ≤ ‖v‖ * ε' := by
          gcongr
          rw [htc y hy, ← dist_eq_norm]
          exact hxy.le
      _ ≤ ε := by
          rw [hε']
          have : ‖v‖ * (ε / (‖v‖ + 1)) = ε * (‖v‖ / (‖v‖ + 1)) := by ring
          rw [this]
          refine mul_le_of_le_one_right hε.le ?_
          exact div_le_one_of_le₀ (by linarith) (by positivity)
  · exact mul_inv_cancel_left (tc y) x
