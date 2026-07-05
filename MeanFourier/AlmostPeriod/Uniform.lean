/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

import MeanFourier.Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# Uniformly almost-periodic functions

This file defines uniformly almost-periodic functions in a group following von Neumann.

For a group `G` and a metric space `X`, a function `f : G → X` is uniformly almost-periodic if for
every `ε > 0` one can cover `G` with finitely many translates of the set of `ε`-almost-periods
`{t : G | ∀ x, dist (f (t⁻¹ * x)) (f x) ≤ ε}`.

We make von Neumann's theory quantitative by keeping track of the "modulus of almost-periodicity",
i.e. for every `ε > 0` of a number `K ε` of translates of the `ε`-almost-period that suffice to
cover `G`.

## Implementation notes

Von Neumann in 1934 defines all three of left almost-periodic (LAP, the one defined above),
right almost-periodic (RAP, same as LAP but replacing left translates with right ones)
and uniformly almost-periodic (UAP, the combination of both). As proven by Maak a year later,
LAP qualitatively implies RAP, meaning we can get away with a single qualitative predicate.
Although the quantitative dependence in Maak's result is poor, we do not introduce a separate
quantitative predicate for RAP functions. This matches the qualitative predicate. We instead suggest
spelling quantitative right-almost periodic functions using precomposition with `MulOpposite.unop`.

## References

* [*Almost periodic functions in a group. I*, John von Neumann](https://doi.org/10.2307/1989792)
* [*Eine neue Definition der fastperiodischen Funktionen*, Wilhelm Maak][maak1935]
-/

public section

open Bornology Metric Real
open scoped Finset NNReal Pointwise

variable {ι 𝕜 G H R X Y E F : Type*} [RCLike 𝕜] [Group G] [Group H] {K L : ℝ → ℝ} {a b x t : G}
  {c : 𝕜}

/-! ## Metric space codomain -/

section MetricSpace
variable [MetricSpace X] [MetricSpace Y] {f g : G → X} {z : X} {ε δ : ℝ}

/-! ### Uniform almost-periods -/

variable (f ε) in
/-- The uniform `ε`-almost-periods of a function `f` from a group `G` to a metric space `X` are
those elements of the group that move `f` by at most `ε` in the L^∞ metric. -/
@[expose]
def uniformAP : Set G := {t | ∀ x, dist (f (t⁻¹ * x)) (f x) ≤ ε}

@[inherit_doc uniformAP] notation3 "AP∞("f ", " ε ")" => uniformAP f ε

/-! #### Basic properties -/

lemma mem_uniformAP : t ∈ AP∞(f, ε) ↔ ∀ x, dist (f (t⁻¹ * x)) (f x) ≤ ε := .rfl

@[simp] lemma one_mem_uniformAP : 1 ∈ AP∞(f, ε) ↔ 0 ≤ ε := by simp [mem_uniformAP]

@[simp] lemma uniformAP_nonempty : AP∞(f, ε).Nonempty ↔ 0 ≤ ε where
  mp := by rintro ⟨t, ht⟩; exact dist_nonneg.trans (ht 1)
  mpr hε := ⟨1, one_mem_uniformAP.2 hε⟩

/-- `a * b⁻¹` is an `ε`-almost-period of `f` iff the two translates `f (a * ·)` and `f (b * ·)` are
at most `ε` away in the L^∞ metric. -/
lemma mul_inv_mem_uniformAP : a * b⁻¹ ∈ AP∞(f, ε) ↔ ∀ x, dist (f (a * x)) (f (b * x)) ≤ ε := by
  simp only [mem_uniformAP, mul_inv_rev, inv_inv]
  exact ((Equiv.mulLeft a).forall_congr <| by simp [dist_comm]).symm

variable (z) in
@[to_fun (attr := simp) uniformAP_fun_const]
lemma uniformAP_const (hε : 0 ≤ ε) : AP∞(Function.const G z, ε) = .univ := by simp [uniformAP, hε]

/-- If `f` is `δ`-uniformly close to `g`, every `ε`-almost-period of `g` is an
`ε + 2δ`-almost-period of `f`. -/
lemma uniformAP_subset_of_forall_dist_le {δ : ℝ} (hfg : ∀ x, dist (f x) (g x) ≤ δ) :
    AP∞(g, ε) ⊆ AP∞(f, ε + 2 * δ) := by
  intro t ht x
  calc dist (f (t⁻¹ * x)) (f x)
      ≤ dist (f (t⁻¹ * x)) (g (t⁻¹ * x)) + dist (g (t⁻¹ * x)) (g x) + dist (g x) (f x) :=
        dist_triangle4 ..
    _ ≤ ε + 2 * δ := by grw [hfg _, ht x, dist_comm, hfg x]; apply le_of_eq; ring_nf

/-! #### Operations on the domain -/

lemma mul_mem_uniformAP {a b : G} {δ : ℝ} (ha : a ∈ AP∞(f, ε)) (hb : b ∈ AP∞(f, δ)) :
    a * b ∈ AP∞(f, ε + δ) := by
  rw [mem_uniformAP] at ha hb
  intro x
  rw [show (a * b)⁻¹ * x = b⁻¹ * (a⁻¹ * x) from by group]
  calc dist (f (b⁻¹ * (a⁻¹ * x))) (f x)
      ≤ dist (f (b⁻¹ * (a⁻¹ * x))) (f (a⁻¹ * x)) + dist (f (a⁻¹ * x)) (f x) :=
        dist_triangle _ (f (a⁻¹ * x)) _
    _ ≤ δ + ε := by grw [hb, ha]
    _ = ε + δ := by ring

lemma uniformAP_mul_uniformAP_subset {δ : ℝ} : AP∞(f, ε) * AP∞(f, δ) ⊆ AP∞(f, ε + δ) := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact mul_mem_uniformAP ha hb

lemma uniformAP_pow_subset : ∀ n : ℕ, AP∞(f, ε) ^ n ⊆ AP∞(f, n * ε)
  | 0 => by simp [mem_uniformAP]
  | n + 1 => by
    grw [pow_succ, uniformAP_pow_subset, uniformAP_mul_uniformAP_subset]
    grind [uniformAP]

@[simp]
lemma inv_mem_uniformAP : t⁻¹ ∈ AP∞(f, ε) ↔ t ∈ AP∞(f, ε) :=
  (Equiv.mulLeft t).forall_congr (by simp [dist_comm])

@[simp]
lemma uniformAP_inv : AP∞(f, ε)⁻¹ = AP∞(f, ε) := by ext t; exact inv_mem_uniformAP

variable (f) in
@[simp]
lemma uniformAP_comp_mulEquiv (φ : H ≃* G) : AP∞(f ∘ φ, ε) = φ ⁻¹' AP∞(f, ε) := by
  ext; simp [mem_uniformAP, φ.surjective.forall]

/-- The almost-periods are unchanged by right translation of the argument. -/
@[simp] lemma uniformAP_comp_mul_right (a : G) : AP∞(fun x ↦ f (x * a), ε) = AP∞(f, ε) := by
  ext t; exact (Equiv.mulRight a).forall_congr <| by simp [mul_assoc]

/-! #### Operations on the codomain -/

/-- The `ε`-almost-periods of a product-valued function are the common `ε`-almost-periods of its two
components. -/
lemma uniformAP_prod {f : G → X × Y} : AP∞(f, ε) = AP∞(Prod.fst ∘ f, ε) ∩ AP∞(Prod.snd ∘ f, ε) := by
  ext t; simp [mem_uniformAP, Prod.dist_eq, forall_and]

/-! ### Quantitative uniformly almost-periodic functions -/

variable (K f) in
/-- For a "modulus of almost-periodicity" `K : ℝ → ℝ`, a function is uniformly `K`-almost-periodic
if its uniform `ε`-almost-periods are `K_ε`-syndetic for all `ε > 0`.

This is a quantitative version of `IsUAP`. -/
@[expose, fun_prop] def IsUAPWith : Prop := ∀ ⦃ε⦄, 0 < ε → CovBySMul G (K ε) .univ AP∞(f, ε)

lemma IsUAPWith.pos (hf : IsUAPWith K f) (hε : 0 < ε) : 0 < K ε := (hf hε).pos (by simp)

lemma IsUAPWith.mono (hKL : ∀ ε > 0, K ε ≤ L ε) (hf : IsUAPWith K f) : IsUAPWith L f :=
  fun _ε hε ↦ (hf hε).mono <| hKL _ hε

@[to_fun (attr := simp, fun_prop)]
protected lemma IsUAPWith.const : IsUAPWith 1 (Function.const G z) := by
  simp +contextual [IsUAPWith, le_of_lt]

/-- Almost-periodicity is quantitatively preserved by uniform limits along any (nontrivial) filter.
-/
lemma IsUAPWith.of_tendstoUniformly {ι : Type*} {p : Filter ι} [p.NeBot] {u : ι → G → X}
    (hu : ∀ᶠ n in p, IsUAPWith K (u n)) (h : TendstoUniformly u f p) :
    IsUAPWith (fun ε ↦ K (ε / 2)) f := by
  intro ε hε
  obtain ⟨n, hn, hu⟩ := ((Metric.tendstoUniformly_iff.1 h (ε / 4) (by positivity)).and hu).exists
  refine (hu <| by positivity).subset_right ?_
  convert uniformAP_subset_of_forall_dist_le (f := f) fun x ↦ (hn x).le
  ring

/-! #### Operations on the domain -/

/-- Almost-periodicity is quantitatively preserved by precomposition with a group isomorphism. -/
lemma IsUAPWith.comp_mulEquiv {φ : H ≃* G} (hf : IsUAPWith K f) : IsUAPWith K (f ∘ φ) := by
  classical
  intro ε hε
  rw [uniformAP_comp_mulEquiv]
  obtain ⟨F, hFK, hcov⟩ := hf hε
  refine ⟨F.image φ.symm, by grw [Finset.card_image_le, hFK], fun h _ ↦ ?_⟩
  obtain ⟨a, ha, s, hs, hgs⟩ := Set.mem_smul.1 (hcov (Set.mem_univ (φ h)))
  rw [smul_eq_mul] at hgs
  exact ⟨φ.symm a, Finset.mem_image_of_mem _  ha, φ.symm s, by simpa using hs, by
    simp [← map_mul, hgs]⟩

@[simp] lemma isUAPWith_comp_mulEquiv {φ : H ≃* G} : IsUAPWith K (f ∘ φ) ↔ IsUAPWith K f where
  mp hf := by simpa [Function.comp_assoc] using hf.comp_mulEquiv (φ := φ.symm)
  mpr := .comp_mulEquiv

@[fun_prop]
lemma IsUAPWith.comp_mul_right (hf : IsUAPWith K f) : IsUAPWith K (fun x ↦ f (x * a)) := by
  simpa [IsUAPWith] using hf

@[fun_prop]
lemma IsUAPWith.comp_mul_left (hf : IsUAPWith K f) : IsUAPWith K (fun x ↦ f (a * x)) := by
  simpa [Function.comp_def, mul_assoc]
    using (hf.comp_mul_right (a := a)).comp_mulEquiv (φ := MulAut.conj a)

@[fun_prop]
protected lemma IsUAPWith.translate (hf : IsUAPWith K f) : IsUAPWith K (τ_[t] f) := hf.comp_mul_left

@[simp] lemma isUAPWith_translate : IsUAPWith K (τ_[t] f) ↔ IsUAPWith K f where
  mp hf := by simpa using hf.translate (t := t⁻¹)
  mpr := .translate

/-- If `f` is left almost-periodic with modulus `K`, then it is right almost-periodic with modulus
`ε ↦ K (ε / 4) ^ K (ε / 4)`. -/
protected lemma IsUAPWith.comp_unop (hf : IsUAPWith K f) :
    IsUAPWith (fun ε ↦ K (ε / 4) ^ K (ε / 4)) (f ∘ MulOpposite.unop) := by
  classical
  intro ε hε
  obtain ⟨F, hFM, hcov⟩ := hf (ε := ε / 4) (by positivity)
  set K₀ := F⁻¹
  have hK₀M : (#K₀ : ℝ) ≤ K (ε / 4) := by simpa [K₀]
  have hK₀ a : ∃ k ∈ K₀, ∀ x, dist (f (a * x)) (f (k * x)) ≤ ε / 4 := by
    obtain ⟨φ, hφ, s, hs, hgs⟩ := hcov (Set.mem_univ a⁻¹)
    refine ⟨φ⁻¹, Finset.inv_mem_inv (Finset.mem_coe.1 hφ), ?_⟩
    simpa [← mul_inv_mem_uniformAP, eq_mul_inv_iff_mul_eq.2 hgs]
  obtain ⟨K', hK'card, hK'⟩ :
      ∃ K' : Finset G, #K' ≤ #K₀ ^ #K₀ ∧ ∀ a, ∃ k ∈ K', ∀ x, dist (f (x * a)) (f (x * k)) ≤ ε := by
    choose k hkK hk using hK₀
    let p (a : G) (κ : K₀) : K₀ := ⟨k (κ * a), hkK _⟩
    have key (a b d : G) (hab : p a = p b) : dist (f (d * a)) (f (d * b)) ≤ ε := by
      replace hab : k (k d * a) = k (k d * b) := congr($hab ⟨k d, hkK d⟩)
      have e1 : dist (f (d * a)) (f (k d * a)) ≤ ε / 4 := hk d a
      have e2 : dist (f (k d * a)) (f (k (k d * a))) ≤ ε / 4 := by simpa using hk (k d * a) 1
      have e3 : dist (f (k (k d * b))) (f (k d * b)) ≤ ε / 4 := by
        rw [dist_comm]; simpa using hk (k d * b) 1
      have e4 : dist (f (k d * b)) (f (d * b)) ≤ ε / 4 := by rw [dist_comm]; exact hk d b
      have hz : dist (f (k (k d * a))) (f (k (k d * b))) = 0 := by rw [hab]; exact dist_self _
      have h1 := dist_triangle (f (d * a)) (f (k d * a)) (f (d * b))
      have h2 := dist_triangle (f (k d * a)) (f (k (k d * a))) (f (d * b))
      have h3 := dist_triangle (f (k (k d * a))) (f (k (k d * b))) (f (d * b))
      have h4 := dist_triangle (f (k (k d * b))) (f (k d * b)) (f (d * b))
      linarith
    let rep (v : K₀ → K₀) : G := if hv : ∃ a, p a = v then hv.choose else 1
    have rep_spec a : p (rep (p a)) = p a := by
      have hv : ∃ a', p a' = p a := ⟨a, rfl⟩; simp [rep, hv, hv.choose_spec]
    exact ⟨Finset.univ.image rep, by grw [Finset.card_image_le]; simp,
      fun a ↦ ⟨rep (p a), by simp, fun x ↦ key _ _ _ (rep_spec a).symm⟩⟩
  refine ⟨(K'.image MulOpposite.op)⁻¹, ?_, ?_⟩
  · grw [Finset.card_inv, Finset.card_image_le, hK'card, Nat.cast_pow, ← rpow_natCast, hK₀M, hK₀M]
    · grw [← hK₀M, ← Nat.cast_nonneg]
    · simp only [Nat.one_le_cast, Finset.one_le_card]
      obtain ⟨k₀, hk₀, -⟩ := hK₀ 1
      exact ⟨k₀, hk₀⟩
  rintro a -
  obtain ⟨k, hk, hka⟩ := hK' a⁻¹.unop
  refine ⟨.op k⁻¹, by simpa, .op k * a, ?_, by simp⟩
  rw [← inv_inv a, mul_inv_mem_uniformAP]
  simpa [dist_comm] using hka

/-- If `f` is right almost-periodic with modulus `K`, then it is left almost-periodic with modulus
`ε ↦ K (ε / 4) ^ K (ε / 4)`. -/
protected lemma IsUAPWith.comp_op {K : ℝ → ℝ} {g : Gᵐᵒᵖ → X} (hg : IsUAPWith K g) :
    IsUAPWith (fun ε ↦ K (ε / 4) ^ K (ε / 4)) (g ∘ .op) :=
  IsUAPWith.comp_mulEquiv (φ := MulEquiv.opOp G) (IsUAPWith.comp_unop hg)

protected lemma IsUAPWith.comp_inv (hf : IsUAPWith K f) :
    IsUAPWith (fun ε ↦ K (ε / 4) ^ K (ε / 4)) (fun x ↦ f x⁻¹) :=
  IsUAPWith.comp_mulEquiv (φ := MulEquiv.inv' G) (IsUAPWith.comp_unop hf)

/-! #### Operations on the codomain -/

/-- Postcomposing a `K`-almost-periodic function `f` with a map `φ` that is uniformly continuous
with modulus `δ` on a set containing the range of `f` gives a `K ∘ δ`-almost-periodic function. -/
@[to_fun (attr := fun_prop)]
protected lemma IsUAPWith.isUniformContinuousOnWith_comp {φ : X → Y} {δ : ℝ → ℝ} {S : Set X}
    (hδ : ∀ ε > 0, 0 < δ ε) (hf : IsUAPWith K f) (hfS : ∀ x, f x ∈ S)
    (hφ : IsUniformContinuousOnWith δ φ S) : IsUAPWith (K ∘ δ) (φ ∘ f) :=
  fun ε hε ↦ (hf (hδ ε hε)).subset_right fun t ht x ↦
    hφ hε (hfS (t⁻¹ * x)) (hfS x) (mem_uniformAP.1 ht x)

/-- Postcomposing a `K`-almost-periodic function with a `C`-Lipschitz map gives a
`ε ↦ K (ε / C)`-almost-periodic function. -/
protected lemma IsUAPWith.lipschitzOnWith_comp {φ : X → Y} {C : ℝ≥0} (hC : 0 < C) {S : Set X}
    (hf : IsUAPWith K f) (hfS : ∀ x, f x ∈ S) (hφ : LipschitzOnWith C φ S) :
    IsUAPWith (fun ε ↦ K (ε / C)) (φ ∘ f) :=
  hf.isUniformContinuousOnWith_comp (fun _ε hε ↦ by positivity) hfS hφ.isUniformContinuousOnWith

/-- A `K`-almost-periodic function to a product is `K`-almost-periodic in its first component. -/
@[to_fun (attr := fun_prop) IsUAPWith.fun_fst]
protected lemma IsUAPWith.fst_comp {f : G → X × Y} (hf : IsUAPWith K f) :
    IsUAPWith K (Prod.fst ∘ f) :=
  fun ε hε ↦ (hf hε).subset_right <| by grw [uniformAP_prod, Set.inter_subset_left]

/-- A `K`-almost-periodic function to a product is `K`-almost-periodic in its second component. -/
@[to_fun (attr := fun_prop) IsUAPWith.fun_snd]
protected lemma IsUAPWith.snd_comp {f : G → X × Y} (hf : IsUAPWith K f) :
    IsUAPWith K (Prod.snd ∘ f) :=
  fun ε hε ↦ (hf hε).subset_right <| by grw [uniformAP_prod, Set.inter_subset_right]

/-- The product of `K`- and `L`-almost-periodic functions is
`ε ↦ K (ε / 2) * L (ε / 2)`-almost-periodic. -/
@[fun_prop]
protected lemma IsUAPWith.prodMk {f : G → X} {g : G → Y} (hf : IsUAPWith K f) (hg : IsUAPWith L g) :
    IsUAPWith (fun ε ↦ K (ε / 2) * L (ε / 2)) fun x ↦ (f x, g x) := by
  rintro ε hε
  replace hε : 0 < ε / 2 := by linarith
  refine ((hf hε).inter (hg hε)).subset_right ?_
  grw [uniformAP_prod, uniformAP_inv, uniformAP_inv, uniformAP_mul_uniformAP_subset,
    uniformAP_mul_uniformAP_subset]
  simp [Function.comp_def]

/-! ### Qualitative uniformly almost-periodic functions -/

variable (f) in
/-- A function is uniformly almost-periodic if its uniform `ε`-almost-periods are syndetic for all
`ε > 0`. -/
@[expose, fun_prop] def IsUAP : Prop := ∀ ⦃ε⦄, 0 < ε → ∃ K, CovBySMul G K .univ AP∞(f, ε)

@[fun_prop] lemma IsUAPWith.isUAP (hf : IsUAPWith K f) : IsUAP f := fun ε hε ↦ ⟨K ε, hf hε⟩

lemma isUAP_iff_exists_isUAPWith : IsUAP f ↔ ∃ K, IsUAPWith K f where
  mp hf := by choose! K hf using hf; exact ⟨K, hf⟩
  mpr := by rintro ⟨K, hf⟩; exact hf.isUAP

alias ⟨IsUAP.exists_isUAPWith, _⟩ := isUAP_iff_exists_isUAPWith

@[to_fun (attr := simp, fun_prop)]
protected lemma IsUAP.const : IsUAP (Function.const G z) := fun ε hε ↦ ⟨1, by simp [hε.le]⟩

@[fun_prop]
protected lemma IsUAP.isBddFun (hf : IsUAP f) : IsBddFun f := by
  -- At `ε = 1`, the almost-periods are syndetic: `univ ⊆ F • AP∞(f, 1)` for some finite `F`.
  obtain ⟨-, F, -, hsub⟩ := hf zero_lt_one
  -- Hence `range f` lies in the finite union of unit balls around the values `f g⁻¹`, `g ∈ F`.
  refine ((isBounded_biUnion F.finite_toSet).2 fun g _ ↦
    isBounded_closedBall (x := f g⁻¹) (r := 1)).subset ?_
  rintro _ ⟨y, rfl⟩
  obtain ⟨g, hg, ht⟩ := Set.mem_smul_iff_inv_smul_mem.1 (hsub (Set.mem_univ y⁻¹))
  refine Set.mem_biUnion hg ?_
  simpa [Metric.mem_closedBall, dist_eq_norm] using ht g⁻¹

/-! #### Operations on the domain -/

/-- Almost-periodicity is preserved by precomposition with a group isomorphism. -/
lemma IsUAP.comp_mulEquiv {H : Type*} [Group H] (φ : H ≃* G) (hf : IsUAP f) :
    IsUAP (f ∘ φ) := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith; exact hf.comp_mulEquiv.isUAP

@[simp] lemma isUAP_comp_mulEquiv {φ : H ≃* G} : IsUAP (f ∘ φ) ↔ IsUAP f := by
  simp [isUAP_iff_exists_isUAPWith]

lemma IsUAP.comp_mul_right (hf : IsUAP f) : IsUAP (fun x ↦ f (x * a)) := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith; exact hf.comp_mul_right.isUAP

lemma IsUAP.comp_mul_left (hf : IsUAP f) : IsUAP (fun x ↦ f (a * x)) := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith; exact hf.comp_mul_left.isUAP

@[fun_prop] protected lemma IsUAP.translate (hf : IsUAP f) : IsUAP (τ_[x] f) := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith; exact hf.translate.isUAP

@[simp] lemma isUAP_translate : IsUAP (τ_[x] f) ↔ IsUAP f where
  mp hf := by simpa using hf.translate (x := x⁻¹)
  mpr := .translate

/-- A function is right almost-periodic iff it is left almost-periodic. -/
@[simp] lemma isUAP_comp_unop : IsUAP (f ∘ MulOpposite.unop) ↔ IsUAP f where
  mp hf := by obtain ⟨K, hf⟩ := hf.exists_isUAPWith; exact hf.comp_op.isUAP
  mpr hf := by obtain ⟨K, hf⟩ := hf.exists_isUAPWith; exact hf.comp_unop.isUAP

alias ⟨_, IsUAP.comp_unop⟩ := isUAP_comp_unop

protected lemma IsUAP.comp_inv (hf : IsUAP f) : IsUAP (fun x ↦ f x⁻¹) := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith; exact hf.comp_inv.isUAP

@[simp] lemma isUAP_comp_inv : IsUAP (fun x ↦ f x⁻¹) ↔ IsUAP f where
  mp hf := by simpa using hf.comp_inv
  mpr := .comp_inv

/-! #### Operations on the codomain -/

/-- Postcomposing a uniformly almost-periodic function with a continuous function gives a uniformly
almost-periodic function. -/
@[to_fun]
protected lemma IsUAP.continuous_comp [ProperSpace X] {φ : X → Y} (hf : IsUAP f)
   (hφ : Continuous φ) : IsUAP (φ ∘ f) := by
  have : Nonempty X := ⟨f 1⟩
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (f 1)).1 hf.isBddFun
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith
  have huc : UniformContinuousOn φ (closedBall (f 1) R) :=
    (isCompact_closedBall ..).uniformContinuousOn_of_continuous hφ.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  choose! δ hδpos hδ using huc
  exact (hf.isUniformContinuousOnWith_comp (δ := fun ε ↦ δ ε / 2)
    (fun ε hε ↦ by have := hδpos ε hε; positivity) (fun x ↦ hR ⟨x, rfl⟩)
    fun ε hε a ha b hb hab ↦ (hδ ε hε a ha b hb <| by have := hδpos ε hε; linarith).le).isUAP

/-- Almost-periodicity is preserved by uniform limits along any (nontrivial) filter. -/
lemma IsUAP.of_tendstoUniformly {ι : Type*} {p : Filter ι} [p.NeBot] {u : ι → G → X}
    (hu : ∀ᶠ n in p, IsUAP (u n)) (h : TendstoUniformly u f p) : IsUAP f := by
  intro ε hε
  obtain ⟨n, hn, hu⟩ := ((Metric.tendstoUniformly_iff.1 h (ε / 3) (by positivity)).and hu).exists
  obtain ⟨K, hu⟩ := hu (ε := ε / 3) (by positivity)
  refine ⟨K, hu.subset_right ?_⟩
  convert uniformAP_subset_of_forall_dist_le (f := f) fun x ↦ (hn x).le
  ring

/-- A product-valued function is uniformly almost-periodic iff both of its components are. -/
lemma isUAP_prod_iff {f : G → X × Y} :
    IsUAP f ↔ IsUAP (Prod.fst ∘ f) ∧ IsUAP (Prod.snd ∘ f) where
  mp hf := by obtain ⟨K, hf⟩ := hf.exists_isUAPWith; exact ⟨hf.fst_comp.isUAP, hf.snd_comp.isUAP⟩
  mpr := by
    rintro ⟨hf, hg⟩
    obtain ⟨K, hf⟩ := hf.exists_isUAPWith
    obtain ⟨L, hg⟩ := hg.exists_isUAPWith
    exact (hf.prodMk hg).isUAP

section MetricSpace
variable [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] {δ : ℝ → ℝ}

lemma closedBall_one_subset_uniformAP_of_isUniformContinuousWith (hf : IsUniformContinuousWith δ f)
    (hε : 0 < ε) : closedBall 1 (δ ε) ⊆ AP∞(f, ε) := by
  rintro t ht x
  rw [mem_closedBall'] at ht
  refine hf hε ?_
  convert ht using 1
  rw [← dist_mul_right _ _ x⁻¹, mul_inv_cancel_right, mul_inv_cancel, ← dist_mul_right _ _ t]
  simp

variable [CompactSpace G]

@[fun_prop]
protected lemma Metric.IsUniformContinuousWith.isUAPWith (hδ : ∀ ε > 0, 0 < δ ε)
    (hf : IsUniformContinuousWith δ f) :
    IsUAPWith (fun ε ↦ (coveringNumber (δ ε).toNNReal (.univ : Set G)).toNat) f := by
  rintro ε hε
  grw [← closedBall_one_subset_uniformAP_of_isUniformContinuousWith hf hε]
  simpa [(hδ _ hε).le] using isCompact_univ.totallyBounded.coveringNumber_ne_top <| by simp [*]

@[fun_prop]
protected lemma UniformContinuous.isUAP (hf : UniformContinuous f) : IsUAP f := by
  obtain ⟨δ, hδ, hf⟩ := uniformContinuous_iff_exists_isUniformContinuousWith.1 hf
  exact (hf.isUAPWith hδ).isUAP

@[fun_prop]
protected lemma Continuous.isUAP (hf : Continuous f) : IsUAP f :=
  (CompactSpace.uniformContinuous_of_continuous hf).isUAP

end MetricSpace

/-! ## Normed additive group codomain -/

section NormedAddCommGroup
variable [NormedAddCommGroup E] [NormedAddCommGroup F] {f g : G → E} {z : E} {ε δ : ℝ}

/-! ### Uniform almost-periods -/

lemma mem_uniformAP_iff_norm : t ∈ AP∞(f, ε) ↔ ∀ x, ‖f (t⁻¹ * x) - f x‖ ≤ ε := by
  simp [mem_uniformAP, dist_eq_norm]

@[simp] lemma uniformAP_zero (hε : 0 ≤ ε) : AP∞((0 : G → E), ε) = .univ :=
  uniformAP_const _ hε

lemma inter_subset_uniformAP_add : AP∞(f, ε) ∩ AP∞(g, δ) ⊆ AP∞(f + g, ε + δ) := by
  rintro t ⟨htf, htg⟩ x
  rw [mem_uniformAP_iff_norm] at htf htg
  rw [dist_eq_norm]
  have : (f + g) (t⁻¹ * x) - (f + g) x = (f (t⁻¹ * x) - f x) + (g (t⁻¹ * x) - g x) := by
    simp only [Pi.add_apply]; abel
  grw [this, norm_add_le, htf x, htg x]

variable (f) in
@[to_fun (attr := simp) uniformAP_fun_smul]
lemma uniformAP_smul [NormedSpace 𝕜 E] (hc : c ≠ 0) : AP∞(c • f, ε) = AP∞(f, ε / ‖c‖) := by
  ext t; simp [mem_uniformAP_iff_norm, ← smul_sub, norm_smul, le_div_iff₀' (norm_pos_iff.2 hc)]

/-! ### Quantitative uniformly almost-periodic functions -/

@[simp, fun_prop]
protected lemma IsUAPWith.zero : IsUAPWith 1 (0 : G → E) := .const

/-- The sum of a `K`- and an `L`-almost-periodic function is
`ε ↦ K (ε / 4) * L (ε / 4)`-almost-periodic. -/
@[to_fun]
protected lemma IsUAPWith.add (hf : IsUAPWith K f) (hg : IsUAPWith L g) :
    IsUAPWith (fun ε ↦ K (ε / 4) * L (ε / 4)) (f + g) := by
  rintro ε hε
  replace hε : (0 : ℝ) < ε / 4 := by linarith
  refine ((hf hε).inter (hg hε)).subset_right ?_
  grw [uniformAP_inv, uniformAP_inv, uniformAP_mul_uniformAP_subset, uniformAP_mul_uniformAP_subset,
    inter_subset_uniformAP_add]
  grind

@[to_fun]
protected lemma IsUAPWith.smul [NormedSpace 𝕜 E] (hf : IsUAPWith K f) (hc : c ≠ 0) :
    IsUAPWith (fun ε ↦ K <| ε / ‖c‖) (c • f) := by
  rintro ε hε
  simp only [ne_eq, hc, not_false_eq_true, uniformAP_smul]
  exact hf <| by positivity

/-! ### Qualitative uniformly almost-periodic functions -/

@[simp, fun_prop] protected lemma IsUAP.zero : IsUAP (0 : G → E) := .const

@[to_fun (attr := fun_prop)]
protected lemma IsUAP.add (hf : IsUAP f) (hg : IsUAP g) : IsUAP (f + g) := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith
  obtain ⟨L, hg⟩ := hg.exists_isUAPWith
  exact (hf.add hg).isUAP

@[to_fun (attr := fun_prop)]
protected lemma IsUAP.smul [NormedSpace 𝕜 E] (hf : IsUAP f) : IsUAP (c • f) := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  · obtain ⟨K, hf⟩ := hf.exists_isUAPWith
    exact (hf.smul hc).isUAP

@[fun_prop]
protected lemma IsUAP.isAlmostConvergent [NormedSpace ℝ E] (hf : IsUAP f) :
    IsAlmostConvergent f := by
  sorry

/-! ### Star -/

section Star
variable [StarAddMonoid E] [NormedStarGroup E]

@[simp] lemma uniformAP_star : AP∞(fun x ↦ star (f x), ε) = AP∞(f, ε) := by
  ext t; simp only [mem_uniformAP_iff_norm, ← star_sub, norm_star]

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

/-- If `t` is an `ε`-almost-period of a `Bf`-bounded function `f` and a `δ`-almost-period of a
`Bg`-bounded function `g`, then it is a `Bg * ε + Bf * δ`-almost-period of `f * g`. -/
lemma inter_subset_uniformAP_mul {Bf Bg δ : ℝ} (hfb : ∀ x, ‖f x‖ ≤ Bf) (hgb : ∀ x, ‖g x‖ ≤ Bg) :
    AP∞(f, ε) ∩ AP∞(g, δ) ⊆ AP∞(f * g, Bg * ε + Bf * δ) := by
  rintro t ⟨htf, htg⟩ x
  rw [mem_uniformAP_iff_norm] at htf htg
  rw [dist_eq_norm]
  have : 0 ≤ Bf := by grw [← hfb 1, ← norm_nonneg]
  have : 0 ≤ ε := by grw [← htf 1, ← norm_nonneg]
  calc ‖(f * g) (t⁻¹ * x) - (f * g) x‖
      = ‖f (t⁻¹ * x) * (g (t⁻¹ * x) - g x) + (f (t⁻¹ * x) - f x) * g x‖ := by
        simp only [Pi.mul_apply]; noncomm_ring
    _ ≤ Bf * δ + ε * Bg := by grw [norm_add_le, norm_mul_le, norm_mul_le, hfb, htg x, htf x, hgb x]
    _ = Bg * ε + Bf * δ := by ring

/-- The product of two uniformly almost-periodic functions is uniformly almost-periodic,
with an explicit modulus depending on the bounds on the norms of `f` and `g`. -/
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

section NormedCommRing
variable [NormedCommRing R] [StarRing R] [NormedStarGroup R] {f : G → R}

open scoped ComplexConjugate in
protected lemma IsUAP.conj (hf : IsUAP f) : IsUAP fun x ↦ conj (f x) := hf.star

end NormedCommRing

noncomputable def unitary_isUAP_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : UnitaryRepresentation ℂ G E) (v w : E) (ε : ℝ) : ℝ :=
  (Metric.coveringNumber (ε / (‖v‖ + 1)).toNNReal (Set.range fun t : G ↦ ρ t w)).toNat

open scoped Pointwise InnerProductSpace Finset in
theorem UnitaryRepresentation.isUAPWith_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : UnitaryRepresentation ℂ G E) (v w : E) :
    IsUAPWith (unitary_isUAP_bound ρ v w) (fun x ↦ ⟪ρ x v, w⟫_ℂ) := by
  intro ε hε
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have horb : TotallyBounded (Set.range fun t : G ↦ ρ t w) := by
    refine (isCompact_closedBall (0 : E) ‖w‖).totallyBounded.subset ?_
    rintro - ⟨t, rfl⟩
    simp
  set ε' : ℝ := ε / (‖v‖ + 1) with hε'
  have hε'pos : 0 < ε' := by positivity
  set r : ℝ≥0 := ε'.toNNReal with hr
  have hrpos : r ≠ 0 := by
    rw [hr, ne_eq, Real.toNNReal_eq_zero, not_le]
    exact hε'pos
  have hcov_ne_top :
      Metric.coveringNumber r (Set.range fun t : G ↦ ρ t w) ≠ ⊤ :=
    TotallyBounded.coveringNumber_ne_top horb hrpos
  set C := Metric.minimalCover r (Set.range fun t : G ↦ ρ t w) with hC
  have hC_subset :
      C ⊆ Set.range fun t : G ↦ ρ t w := Metric.minimalCover_subset
  have hC_finite : C.Finite := Metric.finite_minimalCover
  have hC_cover :
      Metric.IsCover r (Set.range fun t : G ↦ ρ t w) C :=
    Metric.isCover_minimalCover hcov_ne_top
  have hC_encard :
      C.encard = Metric.coveringNumber r (Set.range fun t : G ↦ ρ t w) :=
    Metric.encard_minimalCover hcov_ne_top
  have : Fintype C := Set.Finite.fintype hC_finite
  have hch : ∀ y : C, ∃ t : G, ρ t w = y.1 := fun y ↦ hC_subset y.2
  choose! tc htc using hch
  classical
  set F : Finset G := Finset.univ.image tc
  refine ⟨F, ?_, ?_⟩
  · rw [unitary_isUAP_bound]
    have hF_card : F.card ≤ Fintype.card C := Finset.card_image_le
    have hC_card : Fintype.card C = hC_finite.toFinset.card := hC_finite.card_toFinset.symm
    have hC_toNat : C.encard.toNat = hC_finite.toFinset.card := by
      rw [hC_finite.encard_eq_coe_toFinset_card]
      exact ENat.toNat_coe _
    have hC_encard_toNat :
        C.encard.toNat =
          (Metric.coveringNumber r (Set.range fun t : G ↦ ρ t w)).toNat := by
      rw [hC_encard]
    have hFinal :
        F.card ≤ (Metric.coveringNumber r (Set.range fun t : G ↦ ρ t w)).toNat := by
      omega
    exact Nat.cast_le.2 hFinal
  · rintro x -
    have hx : ρ x w ∈ Set.range fun t : G ↦ ρ t w := ⟨x, rfl⟩
    have hC_cover' := hC_cover
    rw [Metric.isCover_iff_subset_iUnion_closedBall] at hC_cover'
    have hx_mem := hC_cover' hx
    rw [Set.mem_iUnion₂] at hx_mem
    obtain ⟨y, hy, hxy⟩ := hx_mem
    have htc_y : ρ (tc (⟨y, hy⟩ : C)) w = y := htc (⟨y, hy⟩ : C)
    refine ⟨tc (⟨y, hy⟩ : C),
      Finset.mem_image_of_mem _ (Finset.mem_univ (⟨y, hy⟩ : C)),
      (tc (⟨y, hy⟩ : C))⁻¹ * x, ?_, ?_⟩
    · rw [mem_uniformAP]
      intro z
      have hkey : ∀ (s : G) (z' : G), ⟪ρ (s⁻¹ * z') v, w⟫_ℂ = ⟪ρ z' v, ρ s w⟫_ℂ := by
        intro s z'
        have h1 : ρ (s⁻¹ * z') v = (ρ s).symm (ρ z' v) := by simp
        rw [h1]
        calc ⟪(ρ s).symm (ρ z' v), w⟫_ℂ
            = ⟪ρ s ((ρ s).symm (ρ z' v)), ρ s w⟫_ℂ := ((ρ s).inner_map_map _ _).symm
          _ = ⟪ρ z' v, ρ s w⟫_ℂ := by simp
      have h1 : ⟪ρ (((tc (⟨y, hy⟩ : C))⁻¹ * x)⁻¹ * z) v, w⟫_ℂ =
          ⟪ρ (tc (⟨y, hy⟩ : C) * z) v, ρ x w⟫_ℂ := by
        rw [← hkey x (tc (⟨y, hy⟩ : C) * z)]
        have : ((tc (⟨y, hy⟩ : C))⁻¹ * x)⁻¹ * z =
            x⁻¹ * (tc (⟨y, hy⟩ : C) * z) := by group
        rw [this]
      have h2 : ⟪ρ z v, w⟫_ℂ =
          ⟪ρ (tc (⟨y, hy⟩ : C) * z) v, ρ (tc (⟨y, hy⟩ : C)) w⟫_ℂ := by
        rw [← hkey (tc (⟨y, hy⟩ : C)) (tc (⟨y, hy⟩ : C) * z)]
        have : (tc (⟨y, hy⟩ : C))⁻¹ * (tc (⟨y, hy⟩ : C) * z) = z := by group
        rw [this]
      rw [dist_eq_norm, h1, h2, ← inner_sub_right]
      have hr_eq : (r : ℝ) = ε' := Real.coe_toNNReal ε' hε'pos.le
      rw [Metric.mem_closedBall] at hxy
      rw [hr_eq] at hxy
      calc ‖⟪ρ (tc (⟨y, hy⟩ : C) * z) v, ρ x w - ρ (tc (⟨y, hy⟩ : C)) w⟫_ℂ‖
          ≤ ‖ρ (tc (⟨y, hy⟩ : C) * z) v‖ *
            ‖ρ x w - ρ (tc (⟨y, hy⟩ : C)) w‖ := norm_inner_le_norm _ _
        _ = ‖v‖ * ‖ρ x w - ρ (tc (⟨y, hy⟩ : C)) w‖ := by simp
        _ ≤ ‖v‖ * ε' := by
            gcongr
            rw [htc_y, ← dist_eq_norm]
            exact hxy
        _ ≤ ε := by
            rw [hε']
            have : ‖v‖ * (ε / (‖v‖ + 1)) = ε * (‖v‖ / (‖v‖ + 1)) := by ring
            rw [this]
            refine mul_le_of_le_one_right hε.le ?_
            exact div_le_one_of_le₀ (by linarith) (by positivity)
    · exact mul_inv_cancel_left (tc (⟨y, hy⟩ : C)) x

open scoped Pointwise InnerProductSpace Finset in
theorem UnitaryRepresentation.isUAP_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : UnitaryRepresentation ℂ G E) (v w : E) :
    IsUAP fun x ↦ ⟪ρ x v, w⟫_ℂ :=
  (isUAPWith_inner ρ v w).isUAP

