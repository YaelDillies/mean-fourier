/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Additive.CovBySMul
public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import MeanFourier.AlmostConvergent
public import MeanFourier.Mathlib.Algebra.Star.Pi
public import MeanFourier.Mathlib.Data.Finset.Lattice.Fold
public import MeanFourier.Mathlib.Topology.MetricSpace.Pseudo.Defs

import AddCombi.Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import AddCombi.Mathlib.Combinatorics.Additive.CovBySMul
import MeanFourier.Mathlib.Analysis.Normed.Group.Bounded
import MeanFourier.Mathlib.Analysis.Normed.Order.Lattice
import MeanFourier.Mathlib.Analysis.Normed.Ring.Lipschitz
import MeanFourier.Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import MeanFourier.Mathlib.Combinatorics.Additive.CovBySMul
import MeanFourier.Mathlib.Topology.MetricSpace.CoveringNumbers

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
@[fun_prop]
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
  intro t ht x
  simp only [mem_closedBall'] at ht ⊢
  refine hf hε ?_
  grind [dist_mul_right, mul_inv_cancel_right, mul_inv_cancel]

variable [CompactSpace G]

@[fun_prop]
protected lemma Metric.IsUniformContinuousWith.isUAPWith (hδ : ∀ ε > 0, 0 < δ ε)
    (hf : IsUniformContinuousWith δ f) :
    IsUAPWith (fun ε ↦ (coveringNumber (δ ε).toNNReal (.univ : Set G)).toNat) f := by
  rintro ε hε
  grw [← closedBall_one_subset_uniformAP_of_isUniformContinuousWith hf hε]
  simpa [covBySMul_univ_closedBall_iff (hδ ε hε).le] using
    isCompact_univ.totallyBounded.coveringNumber_ne_top (Real.toNNReal_pos.mpr (hδ ε hε)).ne'

@[fun_prop]
protected lemma UniformContinuous.isUAP (hf : UniformContinuous f) : IsUAP f := by
  obtain ⟨δ, hδ, hf⟩ := uniformContinuous_iff_exists_isUniformContinuousWith.1 hf
  exact (hf.isUAPWith hδ).isUAP

@[fun_prop]
protected lemma Continuous.isUAP (hf : Continuous f) : IsUAP f :=
  (CompactSpace.uniformContinuous_of_continuous hf).isUAP

end MetricSpace

/-! ### Functions to a finite product -/

section Pi
variable {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MetricSpace (X i)]
  {f : G → ∀ i, X i} {ε : ℝ}

/-- The `ε`-almost-periods of a function to a finite product are the common `ε`-almost-periods of
its coordinates. -/
lemma uniformAP_pi (hε : 0 ≤ ε) : AP∞(f, ε) = ⋂ i, AP∞(fun x ↦ f x i, ε) := by
  ext t
  simp only [Set.mem_iInter, mem_uniformAP]
  exact ⟨fun h i x ↦ (dist_le_pi_dist _ _ i).trans (h x),
    fun h x ↦ (dist_pi_le_iff hε).2 fun i ↦ h i x⟩

/-- A `K`-almost-periodic function to a finite product is `K`-almost-periodic in each coordinate. -/
protected lemma IsUAPWith.eval {K : ℝ → ℝ} (hf : IsUAPWith K f) (i : ι) :
    IsUAPWith K (fun x ↦ f x i) := fun ε hε ↦
  (hf hε).subset_right fun t (ht : t ∈ AP∞(f, ε)) x ↦ (dist_le_pi_dist _ _ i).trans (ht x)

/-- If each coordinate of a function to a finite product is `Kᵢ`-almost-periodic, then the function
is `(ε ↦ ∏ᵢ Kᵢ(ε / 2))`-almost-periodic. -/
protected lemma IsUAPWith.pi {K : ι → ℝ → ℝ} (hf : ∀ i, IsUAPWith (K i) (fun x ↦ f x i)) :
    IsUAPWith (fun ε ↦ ∏ i, K i (ε / 2)) f := fun ε hε ↦ by
  rw [uniformAP_pi hε.le]
  refine (CovBySMul.iInter (s := .univ) fun i _ ↦ hf i (half_pos hε)).subset_right ?_
  simp only [Finset.mem_univ, Set.iInter_true, uniformAP_inv]
  gcongr with i
  grw [uniformAP_mul_uniformAP_subset, add_halves]

/-- A function to a finite product is uniformly almost-periodic iff each of its coordinates is. -/
lemma isUAP_pi_iff : IsUAP f ↔ ∀ i, IsUAP (fun x ↦ f x i) where
  mp hf i := by obtain ⟨K, hf⟩ := hf.exists_isUAPWith; exact (hf.eval _).isUAP
  mpr hf := by
    choose K hf using fun i ↦ (hf i).exists_isUAPWith
    exact (IsUAPWith.pi hf).isUAP

end Pi
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

@[to_fun (attr := simp) uniformAP_fun_neg]
lemma uniformAP_neg : AP∞(-f, ε) = AP∞(f, ε) := by
  ext t; simp only [mem_uniformAP, Pi.neg_apply, dist_neg_neg]

lemma inter_subset_uniformAP_sub : AP∞(f, ε) ∩ AP∞(g, δ) ⊆ AP∞(f - g, ε + δ) := by
  rintro t ⟨htf, htg⟩ x
  rw [mem_uniformAP_iff_norm] at htf htg
  rw [dist_eq_norm]
  have : (f - g) (t⁻¹ * x) - (f - g) x = (f (t⁻¹ * x) - f x) - (g (t⁻¹ * x) - g x) := by
    simp only [Pi.sub_apply]; abel
  grw [this, norm_sub_le, htf x, htg x]

/-- A common `εᵢ`-almost period of finitely many functions is a `∑ᵢ εᵢ`-almost period of their sum.
-/
lemma iInter_subset_uniformAP_sum {s : Finset ι} {ε : ι → ℝ} {f : ι → G → E} :
    ⋂ i ∈ s, AP∞(f i, ε i) ⊆ AP∞(∑ i ∈ s, f i, ∑ i ∈ s, ε i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    grw [Finset.set_biInter_insert, Finset.sum_insert hj, Finset.sum_insert hj, ih,
      inter_subset_uniformAP_add]

variable (f) in
@[to_fun (attr := simp) uniformAP_fun_smul]
lemma uniformAP_smul [NormedSpace 𝕜 E] (hc : c ≠ 0) : AP∞(c • f, ε) = AP∞(f, ε / ‖c‖) := by
  ext t; simp [mem_uniformAP_iff_norm, ← smul_sub, norm_smul, le_div_iff₀' (norm_pos_iff.2 hc)]

/-! ### Quantitative uniformly almost-periodic functions -/

@[simp, fun_prop]
protected lemma IsUAPWith.zero : IsUAPWith 1 (0 : G → E) := .const

@[to_fun (attr := simp)]
lemma isUAPWith_neg : IsUAPWith K (-f) ↔ IsUAPWith K f := by simp [IsUAPWith]

@[to_fun (attr := fun_prop)]
protected alias ⟨_, IsUAPWith.neg⟩ := isUAPWith_neg

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

/-- A finite sum of uniformly almost-periodic functions is quantitatively uniformly almost-periodic.
-/
protected lemma IsUAPWith.sum {s : Finset ι} (hs : s.Nonempty) {K : ι → ℝ → ℝ} {f : ι → G → E}
    (h : ∀ i ∈ s, IsUAPWith (K i) (f i)) :
    IsUAPWith (fun ε ↦ ∏ i ∈ s, K i (ε / #s / 2)) (∑ i ∈ s, f i) := by
  rintro ε hε
  have hcov : CovBySMul G (∏ i ∈ s, K i (ε / #s / 2)) .univ (⋂ i ∈ s, AP∞(f i, ε / #s)) := by
    refine (CovBySMul.iInter fun i hi ↦ h i hi <| by positivity).subset_right <|
      Set.iInter₂_mono fun i hi ↦ ?_
    rw [uniformAP_inv]
    grw [uniformAP_mul_uniformAP_subset]
    ring_nf
    rfl
  refine hcov.subset_right ?_
  grw [iInter_subset_uniformAP_sum]
  simp
  field_simp
  rfl

@[to_fun]
protected lemma IsUAPWith.smul [NormedSpace 𝕜 E] (hf : IsUAPWith K f) (hc : c ≠ 0) :
    IsUAPWith (fun ε ↦ K <| ε / ‖c‖) (c • f) := by
  rintro ε hε
  simp only [ne_eq, hc, not_false_eq_true, uniformAP_smul]
  exact hf <| by positivity

/-! ### Qualitative uniformly almost-periodic functions -/

@[simp, fun_prop] protected lemma IsUAP.zero : IsUAP (0 : G → E) := .const

@[to_fun (attr := simp)]
lemma isUAP_neg : IsUAP (-f) ↔ IsUAP f := by simp [IsUAP]

@[to_fun (attr := fun_prop)]
protected lemma IsUAP.neg (hf : IsUAP f) : IsUAP (-f) := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith; exact hf.neg.isUAP

@[to_fun (attr := fun_prop)]
protected lemma IsUAP.add (hf : IsUAP f) (hg : IsUAP g) : IsUAP (f + g) := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith
  obtain ⟨L, hg⟩ := hg.exists_isUAPWith
  exact (hf.add hg).isUAP

/-- A finite sum of uniformly almost-periodic functions is uniformly almost-periodic. -/
@[to_fun (attr := fun_prop)]
protected lemma IsUAP.sum {s : Finset ι} {f : ι → G → E} (h : ∀ i ∈ s, IsUAP (f i)) :
    IsUAP (∑ i ∈ s, f i) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · choose! K hf using fun i hi ↦ (h i hi).exists_isUAPWith
    exact (IsUAPWith.sum hs hf).isUAP

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

/-! ### Postcomposition with a normed group operation -/

/-- The difference of a `K`- and an `L`-almost-periodic function is
`ε ↦ K (ε / 4) * L (ε / 4)`-almost-periodic. -/
@[to_fun]
protected lemma IsUAPWith.sub (hf : IsUAPWith K f) (hg : IsUAPWith L g) :
    IsUAPWith (fun ε ↦ K (ε / 4) * L (ε / 4)) (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

@[to_fun (attr := fun_prop)]
protected lemma IsUAP.sub (hf : IsUAP f) (hg : IsUAP g) : IsUAP (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

/-! ### Star -/

section Star
variable [StarAddMonoid E] [NormedStarGroup E]

@[to_fun (attr := simp) uniformAP_fun_star]
lemma uniformAP_star : AP∞(star f, ε) = AP∞(f, ε) := by
  ext t; simp [mem_uniformAP_iff_norm, ← star_sub]

@[to_fun (attr := simp) isUAPWith_fun_star]
lemma isUAPWith_star : IsUAPWith K (star f) ↔ IsUAPWith K f := by simp [IsUAPWith]

@[fun_prop] protected alias ⟨_, IsUAPWith.star⟩ := isUAPWith_star

@[to_fun (attr := simp) isUAP_fun_star]
lemma isUAP_star : IsUAP (star f) ↔ IsUAP f := by simp [IsUAP]

@[fun_prop] protected alias ⟨_, IsUAP.star⟩ := isUAP_star

end Star

/-! ## Lattice codomain -/

section Lattice
variable [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]

/-! ### Uniform almost-periods -/

/-- A common `εᵢ`-almost period of a nonempty finite family of functions is a `∑ᵢ εᵢ`-almost period
of their pointwise supremum. -/
lemma iInter_subset_uniformAP_finsetSup' {s : Finset ι} (hs : s.Nonempty) {g : ι → G → E}
    {ε : ι → ℝ} : ⋂ i ∈ s, AP∞(g i, ε i) ⊆ AP∞(s.sup' hs g, ∑ i ∈ s, ε i) := by
  intro t ht x
  rw [Set.mem_iInter₂] at ht
  rw [dist_eq_norm, Finset.sup'_apply, Finset.sup'_apply]
  calc ‖s.sup' hs (fun i ↦ g i (t⁻¹ * x)) - s.sup' hs (fun i ↦ g i x)‖
      ≤ ∑ i ∈ s, ‖g i (t⁻¹ * x) - g i x‖ := norm_finsetSup'_sub_finsetSup'_le hs _ _
    _ ≤ ∑ i ∈ s, ε i := Finset.sum_le_sum fun i hi ↦ by rw [← dist_eq_norm]; exact ht i hi x

/-- A common `εᵢ`-almost period of a nonempty finite family of functions is a `∑ᵢ εᵢ`-almost period
of their pointwise infimum. -/
lemma iInter_subset_uniformAP_finsetInf' {s : Finset ι} (hs : s.Nonempty) {g : ι → G → E}
    {ε : ι → ℝ} : ⋂ i ∈ s, AP∞(g i, ε i) ⊆ AP∞(s.inf' hs g, ∑ i ∈ s, ε i) := by
  intro t ht x
  rw [Set.mem_iInter₂] at ht
  rw [dist_eq_norm, Finset.inf'_apply, Finset.inf'_apply]
  calc ‖s.inf' hs (fun i ↦ g i (t⁻¹ * x)) - s.inf' hs (fun i ↦ g i x)‖
      ≤ ∑ i ∈ s, ‖g i (t⁻¹ * x) - g i x‖ := norm_finsetInf'_sub_finsetInf'_le hs _ _
    _ ≤ ∑ i ∈ s, ε i := Finset.sum_le_sum fun i hi ↦ by rw [← dist_eq_norm]; exact ht i hi x

/-! ### Quantitative uniformly almost-periodic functions -/

/-- The pointwise supremum of a `K`- and an `L`-almost-periodic function is
`ε ↦ K (ε / 4) * L (ε / 4)`-almost-periodic. -/
@[to_fun (attr := fun_prop)]
protected lemma IsUAPWith.sup (hf : IsUAPWith K f) (hg : IsUAPWith L g) :
    IsUAPWith (fun ε ↦ K (ε / 4) * L (ε / 4)) (f ⊔ g) := by
  convert (hf.prodMk hg).lipschitzOnWith_comp two_pos (fun _ ↦ Set.mem_univ _)
    lipschitzWith_uncurry_sup.lipschitzOnWith using 3
    <;> simp [Pi.sup_def, Function.comp_def] <;> ring_nf

/-- The pointwise infimum of a `K`- and an `L`-almost-periodic function is
`ε ↦ K (ε / 4) * L (ε / 4)`-almost-periodic. -/
@[to_fun (attr := fun_prop)]
protected lemma IsUAPWith.inf (hf : IsUAPWith K f) (hg : IsUAPWith L g) :
    IsUAPWith (fun ε ↦ K (ε / 4) * L (ε / 4)) (f ⊓ g) := by
  convert (hf.prodMk hg).lipschitzOnWith_comp two_pos (fun _ ↦ Set.mem_univ _)
    lipschitzWith_uncurry_inf.lipschitzOnWith using 3
    <;> simp [Pi.inf_def, Function.comp_def] <;> ring_nf

/-- The positive part of a `K`-almost-periodic function is `K`-almost-periodic. -/
@[to_fun (attr := fun_prop)]
protected lemma IsUAPWith.posPart (hf : IsUAPWith K f) : IsUAPWith K f⁺ :=
  (hf.lipschitzOnWith_comp one_pos (fun _ ↦ Set.mem_univ _)
    lipschitzWith_posPart.lipschitzOnWith).mono fun ε _ ↦ le_of_eq (by rw [NNReal.coe_one, div_one])

/-- The negative part of a `K`-almost-periodic function is `K`-almost-periodic. -/
@[to_fun (attr := fun_prop)]
protected lemma IsUAPWith.negPart (hf : IsUAPWith K f) : IsUAPWith K f⁻ :=
  (hf.lipschitzOnWith_comp one_pos (fun _ ↦ Set.mem_univ _)
    lipschitzWith_negPart.lipschitzOnWith).mono fun ε _ ↦ le_of_eq (by rw [NNReal.coe_one, div_one])

/-- The pointwise supremum of a nonempty finite family of uniformly almost-periodic functions is
`ε ↦ ∏ᵢ Kᵢ(ε / #s / 2)`-almost-periodic. -/
@[to_fun (attr := fun_prop)]
protected lemma IsUAPWith.finsetSup' {s : Finset ι} (hs : s.Nonempty) {K : ι → ℝ → ℝ}
    {g : ι → G → E} (h : ∀ i ∈ s, IsUAPWith (K i) (g i)) :
    IsUAPWith (fun ε ↦ ∏ i ∈ s, K i (ε / #s / 2)) (s.sup' hs g) := by
  rintro ε hε
  have hcov : CovBySMul G (∏ i ∈ s, K i (ε / #s / 2)) .univ (⋂ i ∈ s, AP∞(g i, ε / #s)) := by
    refine (CovBySMul.iInter fun i hi ↦ h i hi <| by positivity).subset_right <|
      Set.iInter₂_mono fun i hi ↦ ?_
    rw [uniformAP_inv]
    grw [uniformAP_mul_uniformAP_subset]
    ring_nf
    rfl
  refine hcov.subset_right ?_
  grw [iInter_subset_uniformAP_finsetSup' hs]
  simp
  field_simp
  rfl

/-- The pointwise infimum of a nonempty finite family of uniformly almost-periodic functions is
`ε ↦ ∏ᵢ Kᵢ(ε / #s / 2)`-almost-periodic. -/
@[to_fun (attr := fun_prop)]
protected lemma IsUAPWith.finsetInf' {s : Finset ι} (hs : s.Nonempty) {K : ι → ℝ → ℝ}
    {g : ι → G → E} (h : ∀ i ∈ s, IsUAPWith (K i) (g i)) :
    IsUAPWith (fun ε ↦ ∏ i ∈ s, K i (ε / #s / 2)) (s.inf' hs g) := by
  rintro ε hε
  have hcov : CovBySMul G (∏ i ∈ s, K i (ε / #s / 2)) .univ (⋂ i ∈ s, AP∞(g i, ε / #s)) := by
    refine (CovBySMul.iInter fun i hi ↦ h i hi <| by positivity).subset_right <|
      Set.iInter₂_mono fun i hi ↦ ?_
    rw [uniformAP_inv]
    grw [uniformAP_mul_uniformAP_subset]
    ring_nf
    rfl
  refine hcov.subset_right ?_
  grw [iInter_subset_uniformAP_finsetInf' hs]
  simp
  field_simp
  rfl

/-! ### Qualitative uniformly almost-periodic functions -/

@[to_fun (attr := fun_prop)]
protected lemma IsUAP.sup (hf : IsUAP f) (hg : IsUAP g) : IsUAP (f ⊔ g) := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith
  obtain ⟨L, hg⟩ := hg.exists_isUAPWith
  exact (hf.sup hg).isUAP

@[to_fun (attr := fun_prop)]
protected lemma IsUAP.inf (hf : IsUAP f) (hg : IsUAP g) : IsUAP (f ⊓ g) := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith
  obtain ⟨L, hg⟩ := hg.exists_isUAPWith
  exact (hf.inf hg).isUAP

@[to_fun (attr := fun_prop)]
protected lemma IsUAP.posPart (hf : IsUAP f) : IsUAP f⁺ := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith; exact hf.posPart.isUAP

@[to_fun (attr := fun_prop)]
protected lemma IsUAP.negPart (hf : IsUAP f) : IsUAP f⁻ := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith; exact hf.negPart.isUAP

/-- The pointwise supremum of a nonempty finite family of UAP functions is UAP. -/
@[to_fun (attr := fun_prop)]
protected lemma IsUAP.finsetSup' {s : Finset ι} (hs : s.Nonempty) {g : ι → G → E}
    (h : ∀ i ∈ s, IsUAP (g i)) : IsUAP (s.sup' hs g) :=
  Finset.sup'_induction hs _ (fun _ ha _ hb ↦ IsUAP.sup ha hb) h

/-- The pointwise infimum of a nonempty finite family of UAP functions is UAP. -/
@[to_fun (attr := fun_prop)]
protected lemma IsUAP.finsetInf' {s : Finset ι} (hs : s.Nonempty) {g : ι → G → E}
    (h : ∀ i ∈ s, IsUAP (g i)) : IsUAP (s.inf' hs g) :=
  Finset.inf'_induction hs _ (fun _ ha _ hb ↦ IsUAP.inf ha hb) h

end Lattice

/-! ## Normed ring codomain -/

section NormedRing
variable [NormedRing R] {f g : G → R} {ε : ℝ}

/-! ### Uniform almost-periods -/

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

/-! ### Quantitative uniformly almost-periodic functions -/

/-- The product of a `K`- and an `L`-almost-periodic function is uniformly almost-periodic, with an
explicit modulus depending on the bounds on the norms of `f` and `g`. -/
@[to_fun]
protected lemma IsUAPWith.mul {Bf Bg : ℝ} (hfb : ∀ x, ‖f x‖ ≤ Bf) (hgb : ∀ x, ‖g x‖ ≤ Bg)
    (hf : IsUAPWith K f) (hg : IsUAPWith L g) :
    IsUAPWith (fun ε ↦ K (ε / (Bf + Bg + 1) / 2) * L (ε / (Bf + Bg + 1) / 2)) (f * g) := by
  have hBf : 0 ≤ Bf := (norm_nonneg _).trans (hfb 1)
  have hBg : 0 ≤ Bg := (norm_nonneg _).trans (hgb 1)
  have hC : (0 : ℝ≥0) < Bf.toNNReal + Bg.toNNReal + 1 := by positivity
  have hlip : LipschitzOnWith (Bf.toNNReal + Bg.toNNReal + 1) (fun p : R × R ↦ p.1 * p.2)
      {p | ‖p.1‖ ≤ Bf ∧ ‖p.2‖ ≤ Bg} := by
    have base := lipschitzOnWith_uncurry_mul (R := R) (Bf := Bf.toNNReal) (Bg := Bg.toNNReal)
    rw [lipschitzOnWith_iff_dist_le_mul] at base ⊢
    refine fun p hp q hq ↦ (base p ?_ q ?_).trans ?_
    · simpa [Real.coe_toNNReal _ hBf, Real.coe_toNNReal _ hBg] using hp
    · simpa [Real.coe_toNNReal _ hBf, Real.coe_toNNReal _ hBg] using hq
    · exact mul_le_mul_of_nonneg_right (by push_cast; linarith) dist_nonneg
  change IsUAPWith _ (fun x ↦ f x * g x)
  simpa [Function.comp_def, NNReal.coe_add, NNReal.coe_one, Real.coe_toNNReal _ hBf,
    Real.coe_toNNReal _ hBg] using (hf.prodMk hg).lipschitzOnWith_comp hC
    (fun x ↦ show (f x, g x) ∈ {p : R × R | ‖p.1‖ ≤ Bf ∧ ‖p.2‖ ≤ Bg} from ⟨hfb x, hgb x⟩) hlip

/-- A natural power of a `K`-almost-periodic function bounded above by `B` is
`ε ↦ K (ε / (n * Bⁿ⁻¹ + 1))`-almost-periodic. -/
@[to_fun]
protected lemma IsUAPWith.pow {B : ℝ} (n : ℕ) (hfb : ∀ x, ‖f x‖ ≤ B) (hf : IsUAPWith K f) :
    IsUAPWith (fun ε ↦ K (ε / (n * B ^ (n - 1) + 1))) (f ^ n) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hfb 1)
  change IsUAPWith _ (fun x ↦ f x ^ n)
  simpa [Function.comp_def] using hf.isUniformContinuousOnWith_comp
    (fun ε hε ↦ by positivity) (fun x ↦ hfb x) (isUniformContinuousOnWith_pow n hB)

/-! ### Qualitative uniformly almost-periodic functions -/

@[to_fun (attr := fun_prop)]
protected lemma IsUAP.mul (hf : IsUAP f) (hg : IsUAP g) : IsUAP (f * g) := by
  obtain ⟨Bf, hBf⟩ := hf.isBddFun.exists_forall_norm_le
  obtain ⟨Bg, hBg⟩ := hg.isBddFun.exists_forall_norm_le
  obtain ⟨K, hf'⟩ := hf.exists_isUAPWith
  obtain ⟨L, hg'⟩ := hg.exists_isUAPWith
  exact (hf'.mul hBf hBg hg').isUAP

/-- A natural power of an almost-periodic function is almost-periodic. -/
@[to_fun (attr := fun_prop)]
protected lemma IsUAP.pow (hf : IsUAP f) : ∀ n : ℕ, IsUAP (f ^ n)
  | 0 => by simpa using IsUAP.const (z := (1 : R))
  | n + 1 => by rw [pow_succ]; exact (hf.pow n).mul hf

end NormedRing

/-! ## Normed commutative ring codomain -/

section NormedCommRing
variable [NormedCommRing R]

/-! ### Uniform almost-periods -/

/-- A common `εᵢ`-almost period of finitely many `Bᵢ`-bounded functions is an
`∑ᵢ (∏_{j ≠ i} Bⱼ) εᵢ`-almost period of their product. -/
lemma iInter_subset_uniformAP_prod [NormOneClass R] {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {g : ι → G → R} {B : ι → ℝ} {ε : ι → ℝ} (hB : ∀ i x, ‖g i x‖ ≤ B i) :
    (⋂ i ∈ s, AP∞(g i, ε i)) ⊆
      AP∞(∏ i ∈ s, g i, ∑ i ∈ s, (∏ j ∈ s.erase i, B j) * ε i) := by
  have hprod (t : Finset ι) (x) : ‖(∏ i ∈ t, g i) x‖ ≤ ∏ i ∈ t, B i := by
    grw [Finset.prod_apply, Finset.norm_prod_le]; gcongr with i; exact hB i x
  induction s using Finset.induction with
  | empty => simpa using uniformAP_const (1 : R) le_rfl
  | insert j s hj ih =>
    rw [Finset.set_biInter_insert, Finset.prod_insert hj]
    have hbound : ∑ i ∈ insert j s, (∏ k ∈ (insert j s).erase i, B k) * ε i
        = (∏ i ∈ s, B i) * ε j + B j * ∑ i ∈ s, (∏ k ∈ s.erase i, B k) * ε i := by
      rw [Finset.sum_insert hj, Finset.erase_insert hj, Finset.mul_sum]
      congr! 2 with i hi
      rw [Finset.erase_insert_of_ne (ne_of_mem_of_not_mem hi hj).symm,
        Finset.prod_insert fun hji ↦ hj (Finset.mem_of_mem_erase hji)]
      ring
    rw [hbound]
    exact (Set.inter_subset_inter_right _ ih).trans
      (inter_subset_uniformAP_mul (fun x ↦ hB j x) fun x ↦ hprod s x)

/-! ### Quantitative uniformly almost-periodic functions -/

omit [NormedCommRing R] in
/-- Finitary `IsUAPWith.mul`: a finite product of uniformly almost-periodic functions is uniformly
almost-periodic, with an explicit modulus depending on the bounds `Bᵢ` on the `gᵢ`. -/
@[to_fun]
protected lemma IsUAPWith.prod [NormedCommRing R] [NormOneClass R] {ι : Type*} [DecidableEq ι]
    [Fintype ι] {g : ι → G → R} {B : ι → ℝ} {K : ι → ℝ → ℝ} (hB : ∀ i x, ‖g i x‖ ≤ B i)
    (h : ∀ i, IsUAPWith (K i) (g i)) :
    IsUAPWith (fun ε ↦ ∏ i, K i (ε / (∑ i, ∏ j ≠ i, B j + 1) / 2))
      (∏ i, g i) := fun ε hε ↦ by
  have hBnn (i) : 0 ≤ B i := (norm_nonneg _).trans (hB i 1)
  set S := ∑ i, ∏ j ∈ Finset.univ.erase i, B j with hSdef
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ Finset.prod_nonneg fun j _ ↦ hBnn j
  have hδ : 0 < ε / (S + 1) := div_pos hε (by linarith)
  have hcov : CovBySMul G (∏ i, K i (ε / (S + 1) / 2)) Set.univ (⋂ i, AP∞(g i, ε / (S + 1))) := by
    refine (CovBySMul.iInter (s := Finset.univ) fun i _ ↦ h i (half_pos hδ)).subset_right ?_
    simp only [Finset.mem_univ, Set.iInter_true]
    exact Set.iInter_mono fun i ↦ by
      rw [uniformAP_inv]
      exact uniformAP_mul_uniformAP_subset.trans (subset_of_eq (by rw [add_halves]))
  refine hcov.subset_right ?_
  have hstep := iInter_subset_uniformAP_prod (s := Finset.univ) (g := g) (B := B)
    (ε := fun _ ↦ ε / (S + 1)) hB
  simp only [Finset.mem_univ, Set.iInter_true] at hstep
  refine hstep.trans fun t ht x ↦ (ht x).trans ?_
  rw [← Finset.sum_mul, ← hSdef, ← mul_div_assoc, div_le_iff₀ (by linarith : (0:ℝ) < S + 1)]
  nlinarith [hε.le, hSnn]

/-! ### Qualitative uniformly almost-periodic functions -/

/-- Finitary `IsUAP.mul`: a finite product of almost-periodic functions is almost periodic. -/
@[to_fun (attr := fun_prop)]
protected lemma IsUAP.prod {ι : Type*} {s : Finset ι} {g : ι → G → R}
    (h : ∀ i ∈ s, IsUAP (g i)) : IsUAP (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using IsUAPWith.isUAP (IsUAPWith.const (z := (1 : R)))
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    exact IsUAP.mul (h j (Finset.mem_insert_self _ _))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

variable [StarRing R] [NormedStarGroup R] {f : G → R}

open scoped ComplexConjugate in
@[to_fun (attr := fun_prop)]
protected lemma IsUAP.conj (hf : IsUAP f) : IsUAP (conj f) := hf.star

end NormedCommRing

/-! ## Normed field codomain -/

section NormedField
variable [NormedField R] {f g : G → R} {ε : ℝ}

/-! ### Uniform almost-periods -/

/-- Inversion is uniformly continuous on the set of elements of norm at least `c > 0`, with modulus
`ε ↦ c ^ 2 * ε`. -/
lemma isUniformContinuousOnWith_inv {c : ℝ} (hc : 0 < c) :
    IsUniformContinuousOnWith (fun ε ↦ c ^ 2 * ε) (Inv.inv : R → R) {y | c ≤ ‖y‖} := by
  rintro ε hε a ha b hb hab
  rw [Set.mem_ofPred_eq] at ha hb
  have ha0 : a ≠ 0 := norm_pos_iff.1 (hc.trans_le ha)
  have hb0 : b ≠ 0 := norm_pos_iff.1 (hc.trans_le hb)
  rw [dist_eq_norm, inv_sub_inv ha0 hb0, norm_div, norm_mul, div_le_iff₀ (by positivity),
    show ‖b - a‖ = dist a b from by rw [dist_eq_norm, norm_sub_rev]]
  have hc2 : c ^ 2 ≤ ‖a‖ * ‖b‖ := by rw [sq]; gcongr
  nlinarith [hab, mul_le_mul_of_nonneg_right hc2 hε.le]

/-! ### Quantitative uniformly almost-periodic functions -/

/-- The inverse of a `K`-almost-periodic function bounded below by `c > 0` is
`ε ↦ K (c ^ 2 * ε)`-almost-periodic. -/
protected lemma IsUAPWith.inv_comp {c : ℝ} (hc : 0 < c) (hfc : ∀ x, c ≤ ‖f x‖)
    (hf : IsUAPWith K f) : IsUAPWith (fun ε ↦ K (c ^ 2 * ε)) (fun x ↦ (f x)⁻¹) := by
  simpa [Function.comp_def] using hf.isUniformContinuousOnWith_comp
    (fun ε hε ↦ by positivity) (fun x ↦ hfc x) (isUniformContinuousOnWith_inv hc)

/-- The quotient of a `K`-almost-periodic function bounded above by `Bf` and an `L`-almost-periodic
function bounded below by `c > 0` is uniformly almost-periodic. -/
protected lemma IsUAPWith.div {Bf c : ℝ} (hfb : ∀ x, ‖f x‖ ≤ Bf) (hc : 0 < c)
    (hgc : ∀ x, c ≤ ‖g x‖) (hf : IsUAPWith K f) (hg : IsUAPWith L g) :
    IsUAPWith (fun ε ↦ K (ε / (Bf + c⁻¹ + 1) / 2) * L (c ^ 2 * (ε / (Bf + c⁻¹ + 1) / 2)))
      (f / g) := by
  have hgb : ∀ x, ‖(g x)⁻¹‖ ≤ c⁻¹ := fun x ↦ by rw [norm_inv]; exact inv_anti₀ hc (hgc x)
  rw [div_eq_mul_inv]
  exact hf.mul hfb hgb (hg.inv_comp hc hgc)

/-- An integer power of a `K`-almost-periodic function bounded above by `B` and below by `c > 0` is
quantitatively uniformly almost-periodic, with the maximum of the moduli of the two cases. -/
protected lemma IsUAPWith.zpow (n : ℤ) {B c : ℝ} (hc : 0 < c) (hfc : ∀ x, c ≤ ‖f x‖)
    (hfb : ∀ x, ‖f x‖ ≤ B) (hf : IsUAPWith K f) :
    IsUAPWith (fun ε ↦ K (ε / (n.natAbs * B ^ (n.natAbs - 1) + 1)) ⊔
      K ((c ^ n.natAbs) ^ 2 * ε / (n.natAbs * B ^ (n.natAbs - 1) + 1))) (f ^ n) := by
  have hbnd : ∀ m : ℕ, ∀ x, c ^ m ≤ ‖(f ^ m) x‖ := fun m x ↦ by
    rw [Pi.pow_apply, norm_pow]; gcongr; exact hfc x
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast]
    simp only [Int.natAbs_natCast]
    exact (hf.pow m hfb).mono fun ε _ ↦ le_max_left ..
  · rw [zpow_neg, zpow_natCast]
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    exact ((hf.pow m hfb).inv_comp (c := c ^ m) (by positivity) (hbnd m)).mono
      fun ε _ ↦ le_max_right ..

/-! ### Qualitative uniformly almost-periodic functions -/

/-- The inverse of an almost-periodic function bounded away from `0` is almost-periodic. -/
@[to_fun (attr := fun_prop)]
protected lemma IsUAP.inv {c : ℝ} (hc : 0 < c) (hfc : ∀ x, c ≤ ‖f x‖) (hf : IsUAP f) :
    IsUAP f⁻¹ := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith; exact (hf.inv_comp hc hfc).isUAP

/-- The quotient of an almost-periodic function by an almost-periodic function bounded away from `0`
is almost-periodic. -/
@[to_fun (attr := fun_prop)]
protected lemma IsUAP.div {c : ℝ} (hc : 0 < c) (hgc : ∀ x, c ≤ ‖g x‖) (hf : IsUAP f)
    (hg : IsUAP g) : IsUAP (f / g) := by
  rw [div_eq_mul_inv]; exact hf.mul (hg.inv hc hgc)

/-- An integer power of an almost-periodic function bounded away from `0` is almost-periodic. -/
@[to_fun (attr := fun_prop)]
protected lemma IsUAP.zpow {c : ℝ} (hc : 0 < c) (hfc : ∀ x, c ≤ ‖f x‖) (hf : IsUAP f) :
    ∀ n : ℤ, IsUAP (f ^ n)
  | (n : ℕ) => by rw [zpow_natCast]; exact hf.pow n
  | .negSucc n => by rw [zpow_negSucc, ← inv_pow]; exact (hf.inv hc hfc).pow _

end NormedField

/-! ## Real-valued functions -/

section Real
variable {f : G → ℝ}

/-- A real power `r` of a `K`-almost-periodic function with values in `[c, B]` (`0 < c`) is
`ε ↦ K (ε / (|r| * (c ^ (r - 1) ⊔ B ^ (r - 1)) + 1))`-almost-periodic. -/
@[to_fun]
protected lemma IsUAPWith.rpow (r : ℝ) {c B : ℝ} (hc : 0 < c) (hfc : ∀ x, c ≤ f x)
    (hfb : ∀ x, f x ≤ B) (hf : IsUAPWith K f) :
    IsUAPWith (fun ε ↦ K (ε / (|r| * (c ^ (r - 1) ⊔ B ^ (r - 1)) + 1))) (f ^ r) := by
  have hcp : (0 : ℝ) < c ^ (r - 1) ⊔ B ^ (r - 1) := (Real.rpow_pos_of_pos hc _).trans_le le_sup_left
  have hC0 : 0 ≤ |r| * (c ^ (r - 1) ⊔ B ^ (r - 1)) := mul_nonneg (abs_nonneg _) hcp.le
  have hpos : (0 : ℝ≥0) < (|r| * (c ^ (r - 1) ⊔ B ^ (r - 1))).toNNReal + 1 := by positivity
  have hlip : LipschitzOnWith ((|r| * (c ^ (r - 1) ⊔ B ^ (r - 1))).toNNReal + 1)
      (· ^ r : ℝ → ℝ) (Set.Icc c B) :=
    lipschitzOnWith_iff_dist_le_mul.2 fun a ha b hb ↦
      (lipschitzOnWith_iff_dist_le_mul.1 (lipschitzOnWith_rpow r hc) a ha b hb).trans
        (mul_le_mul_of_nonneg_right (by push_cast; linarith) dist_nonneg)
  simpa [Function.comp_def, NNReal.coe_add, NNReal.coe_one, Real.coe_toNNReal _ hC0, Pi.pow_def]
    using hf.lipschitzOnWith_comp hpos (fun x ↦ Set.mem_Icc.2 ⟨hfc x, hfb x⟩) hlip

end Real

/-! ## Complex-valued functions -/

section Complex
variable {f : G → ℂ}

open Complex in
/-- A complex power `w` of a `K`-almost-periodic function whose values lie in a convex subset `S` of
the slit plane with norms in `[c, B]` (`0 < c`) is
`ε ↦ K (ε / (‖w‖ * (c ^ (w.re - 1) ⊔ B ^ (w.re - 1)) * exp (π * |w.im|) + 1))`-almost-periodic. -/
@[to_fun]
protected lemma IsUAPWith.cpow (w : ℂ) {c B : ℝ} {S : Set ℂ} (hc : 0 < c) (hS : Convex ℝ S)
    (hSslit : S ⊆ slitPlane) (hSc : ∀ z ∈ S, c ≤ ‖z‖) (hSB : ∀ z ∈ S, ‖z‖ ≤ B)
    (hfS : ∀ x, f x ∈ S) (hf : IsUAPWith K f) :
    IsUAPWith
      (fun ε ↦ K (ε / (‖w‖ * (c ^ (w.re - 1) ⊔ B ^ (w.re - 1)) * Real.exp (Real.pi * |w.im|) + 1)))
      (f ^ w) := by
  have hsup : (0 : ℝ) < c ^ (w.re - 1) ⊔ B ^ (w.re - 1) :=
    (Real.rpow_pos_of_pos hc _).trans_le le_sup_left
  have hC0 : 0 ≤ ‖w‖ * (c ^ (w.re - 1) ⊔ B ^ (w.re - 1)) * Real.exp (Real.pi * |w.im|) := by
    positivity
  have hpos : (0 : ℝ≥0) <
      (‖w‖ * (c ^ (w.re - 1) ⊔ B ^ (w.re - 1)) * Real.exp (Real.pi * |w.im|)).toNNReal + 1 := by
    positivity
  have hlip : LipschitzOnWith
      ((‖w‖ * (c ^ (w.re - 1) ⊔ B ^ (w.re - 1)) * Real.exp (Real.pi * |w.im|)).toNNReal + 1)
      (· ^ w : ℂ → ℂ) S :=
    lipschitzOnWith_iff_dist_le_mul.2 fun a ha b hb ↦
      (lipschitzOnWith_iff_dist_le_mul.1
        (lipschitzOnWith_cpow w hc hS hSslit hSc hSB) a ha b hb).trans
        (mul_le_mul_of_nonneg_right (by push_cast; linarith) dist_nonneg)
  simpa [Function.comp_def, NNReal.coe_add, NNReal.coe_one, Real.coe_toNNReal _ hC0, Pi.pow_def]
    using hf.lipschitzOnWith_comp hpos hfS hlip

end Complex
