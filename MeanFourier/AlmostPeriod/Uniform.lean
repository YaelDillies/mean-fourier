/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MeanFourier.AlmostConvergent
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
* [*Eine neue Definition der fastperiodischen Funktionen*, Wilhelm Maak][maak1935]
-/

public section

open Bornology Metric Real
open scoped Finset Pointwise

variable {𝕜 G H R E : Type*} [RCLike 𝕜] [Group G] [Group H] {K L : ℝ → ℝ} {a b x t : G} {c : 𝕜}

section NormedAddCommGroup
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f g : G → E} {z : E} {ε : ℝ}

variable (f ε) in
/-- The uniform `ε`-almost periods of a function `f` from a group `G` to a normed space `E` are
those elements of the group that move `f` by at most `ε` in L^∞ norm. -/
@[expose]
def uniformAP : Set G := {t | ∀ x, ‖f (t⁻¹ * x) - f x‖ ≤ ε}

@[inherit_doc uniformAP] notation3 "AP∞("f ", " ε ")" => uniformAP f ε

lemma mem_uniformAP : t ∈ AP∞(f, ε) ↔ ∀ x, ‖f (t⁻¹ * x) - f x‖ ≤ ε := .rfl

@[simp] lemma one_mem_uniformAP : 1 ∈ AP∞(f, ε) ↔ 0 ≤ ε := by simp [mem_uniformAP]

@[simp] lemma uniformAP_nonempty : AP∞(f, ε).Nonempty ↔ 0 ≤ ε where
  mp := by rintro ⟨t, ht⟩; exact (norm_nonneg _).trans (ht 1)
  mpr hε := ⟨1, one_mem_uniformAP.2 hε⟩

@[simp]
lemma inv_mem_uniformAP : t⁻¹ ∈ AP∞(f, ε) ↔ t ∈ AP∞(f, ε) :=
  (Equiv.mulLeft t).forall_congr (by simp [norm_sub_rev])

@[simp]
lemma uniformAP_inv : AP∞(f, ε)⁻¹ = AP∞(f, ε) := by ext t; exact inv_mem_uniformAP

/-- `a * b⁻¹` is an `ε`-almost-period of `f` iff the two translatess `f (a * ·)` and `f (b * ·)` are
at most `ε` away in L^∞ norm. -/
lemma mul_inv_mem_uniformAP : a * b⁻¹ ∈ AP∞(f, ε) ↔ ∀ x, ‖f (a * x) - f (b * x)‖ ≤ ε := by
  simp only [mem_uniformAP, mul_inv_rev, inv_inv]
  exact ((Equiv.mulLeft a).forall_congr <| by simp [norm_sub_rev]).symm

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

variable (z) in
@[to_fun (attr := simp) uniformAP_fun_const]
lemma uniformAP_const (hε : 0 ≤ ε) : AP∞(Function.const G z, ε) = .univ := by simp [uniformAP, hε]

variable (f) in
@[to_fun (attr := simp) uniformAP_fun_smul]
lemma uniformAP_smul (hc : c ≠ 0) : AP∞(c • f, ε) = AP∞(f, ε / ‖c‖) := by
  ext t; simp [mem_uniformAP, ← smul_sub, norm_smul, le_div_iff₀' (norm_pos_iff.2 hc)]

variable (f) in
@[simp]
lemma uniformAP_comp_mulEquiv (φ : H ≃* G) : AP∞(f ∘ φ, ε) = φ ⁻¹' AP∞(f, ε) := by
  ext; simp [mem_uniformAP, φ.surjective.forall]

/-- The almost periods are unchanged by right translation of the argument. -/
@[simp] lemma uniformAP_comp_mul_right (a : G) : AP∞(fun x ↦ f (x * a), ε) = AP∞(f, ε) := by
  ext t; exact (Equiv.mulRight a).forall_congr <| by simp [mul_assoc]

/-- If `f` is `δ`-uniformly close to `g`, every `ε`-almost period of `g` is an `(ε + 2δ)`-almost
period of `f`. -/
lemma uniformAP_subset_of_forall_norm_sub_le {δ : ℝ} (hfg : ∀ x, ‖f x - g x‖ ≤ δ) :
    AP∞(g, ε) ⊆ AP∞(f, ε + 2 * δ) := by
  intro t ht x
  grw [norm_sub_le_norm_sub_add_norm_sub _ (g x), norm_sub_le_norm_sub_add_norm_sub _ (g (t⁻¹ * x)),
    hfg _, ht x, norm_sub_rev, hfg x]
  apply le_of_eq
  ring

variable (K f) in
/-- For a "modulus of almost-periodicity" `K : ℝ → ℝ`,a function is uniformly `K`-almost-periodic
if its uniform `ε`-almost periods are `K_ε`-syndetic for all `ε > 0`.

This is a quantitative version of `IsUAP`. -/
@[expose, fun_prop] def IsUAPWith : Prop := ∀ ⦃ε⦄, 0 < ε → CovBySMul G (K ε) .univ AP∞(f, ε)

lemma IsUAPWith.pos (hf : IsUAPWith K f) (hε : 0 < ε) : 0 < K ε := (hf hε).pos (by simp)

lemma IsUAPWith.mono (hKL : ∀ ε > 0, K ε ≤ L ε) (hf : IsUAPWith K f) : IsUAPWith L f :=
  fun _ε hε ↦ (hf hε).mono <| hKL _ hε

@[to_fun (attr := simp, fun_prop)]
protected lemma IsUAPWith.const : IsUAPWith 1 (Function.const G z) := by
  simp +contextual [IsUAPWith, le_of_lt]

@[simp, fun_prop]
protected lemma IsUAPWith.zero : IsUAPWith 1 (0 : G → E) := .const

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

/-- Almost periodicity is quantitatively preserved by precomposition with a group isomorphism. -/
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

/-- Almost periodicity is quantitatively preserved by uniform limits along any (nontrivial) filter.
-/
lemma IsUAPWith.of_tendstoUniformly {ι : Type*} {p : Filter ι} [p.NeBot] {u : ι → G → E}
    (hu : ∀ᶠ n in p, IsUAPWith K (u n)) (h : TendstoUniformly u f p) :
    IsUAPWith (fun ε ↦ K (ε / 3)) f := by
  intro ε hε
  obtain ⟨n, hn, hu⟩ := ((Metric.tendstoUniformly_iff.1 h (ε / 3) (by positivity)).and hu).exists
  refine (hu <| by positivity).subset_right ?_
  convert uniformAP_subset_of_forall_norm_sub_le (f := f) fun x ↦ by
    simpa [dist_eq_norm] using (hn x).le
  ring

/-- If `f` is left almost-periodic with modulus `K`, then it is right almost-periodic with modulus
`ε ↦ K (ε / 4) ^ K (ε / 4)`. -/
protected lemma IsUAPWith.comp_unop (hf : IsUAPWith K f) :
    IsUAPWith (fun ε ↦ K (ε / 4) ^ K (ε / 4)) (f ∘ MulOpposite.unop) := by
  classical
  intro ε hε
  obtain ⟨F, hFM, hcov⟩ := hf (ε := ε / 4) (by positivity)
  set K₀ := F⁻¹
  have hK₀M : (#K₀ : ℝ) ≤ K (ε / 4) := by simpa [K₀]
  have hK₀ a : ∃ k ∈ K₀, ∀ x, ‖f (a * x) - f (k * x)‖ ≤ ε / 4 := by
    obtain ⟨φ, hφ, s, hs, hgs⟩ := hcov (Set.mem_univ a⁻¹)
    refine ⟨φ⁻¹, Finset.inv_mem_inv (Finset.mem_coe.1 hφ), ?_⟩
    simpa [← mul_inv_mem_uniformAP, eq_mul_inv_iff_mul_eq.2 hgs]
  obtain ⟨K', hK'card, hK'⟩ :
      ∃ K' : Finset G, #K' ≤ #K₀ ^ #K₀ ∧ ∀ a, ∃ k ∈ K', ∀ x, ‖f (x * a) - f (x * k)‖ ≤ ε := by
    choose k hkK hk using hK₀
    let p (a : G) (κ : K₀) : K₀ := ⟨k (κ * a), hkK _⟩
    have key (a b d : G) (hab : p a = p b) : ‖f (d * a) - f (d * b)‖ ≤ ε := by
      replace hab : k (k d * a) = k (k d * b) := congr($hab ⟨k d, hkK d⟩)
      have ea : ‖f (k d * a) - f (k (k d * a))‖ ≤ ε / 4 := by simpa using hk (k d * a) 1
      have eb : ‖f (k d * b) - f (k (k d * b))‖ ≤ ε / 4 := by simpa using hk (k d * b) 1
      grw [norm_sub_le_norm_sub_add_norm_sub _ (f (k d * a)), hk,
        norm_sub_le_norm_sub_add_norm_sub _ (f (k (k d * a))), ea, hab,
        norm_sub_le_norm_sub_add_norm_sub _ (f (k d * b)), norm_sub_rev, eb, norm_sub_rev, hk]
      apply le_of_eq
      ring
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
  simpa [norm_sub_rev] using hka

/-- If `f` is right almost-periodic with modulus `K`, then it is left almost-periodic with modulus
`ε ↦ K (ε / 4) ^ K (ε / 4)`. -/
protected lemma IsUAPWith.comp_op {K : ℝ → ℝ} {g : Gᵐᵒᵖ → E} (hg : IsUAPWith K g) :
    IsUAPWith (fun ε ↦ K (ε / 4) ^ K (ε / 4)) (g ∘ .op) :=
  IsUAPWith.comp_mulEquiv (φ := MulEquiv.opOp G) (IsUAPWith.comp_unop hg)

lemma IsUAPWith.comp_mul_right (hf : IsUAPWith K f) : IsUAPWith K (fun x ↦ f (x * a)) := by
  simpa [IsUAPWith] using hf

lemma IsUAPWith.comp_mul_left (hf : IsUAPWith K f) :
    IsUAPWith (fun ε ↦ K (ε / 16) ^ K (ε / 16) ^ (K (ε / 16) + 1)) (fun x ↦ f (a * x)) := by
  refine hf.comp_unop.comp_mul_right (a := .op a).comp_op.mono fun ε hε ↦ ?_
  · rw [rpow_add_one (hf.pos <| by positivity).ne', mul_comm, rpow_mul (hf.pos <| by positivity).le]
    apply le_of_eq
    ring_nf

protected lemma IsUAPWith.comp_inv {K : ℝ → ℝ} (hf : IsUAPWith K f) :
    IsUAPWith (fun ε ↦ K (ε / 4) ^ K (ε / 4)) (fun x ↦ f x⁻¹) :=
  IsUAPWith.comp_mulEquiv (φ := MulEquiv.inv' G) (IsUAPWith.comp_unop hf)

@[fun_prop]
protected lemma IsUAPWith.translate (hf : IsUAPWith K f) :
    IsUAPWith (fun ε ↦ K (ε / 16) ^ K (ε / 16) ^ (K (ε / 16) + 1)) (τ_[t] f) :=
  hf.comp_mul_left

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
lemma IsUAP.comp_mulEquiv {H : Type*} [Group H] (φ : H ≃* G) (hf : IsUAP f) :
    IsUAP (f ∘ φ) := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith; exact hf.comp_mulEquiv.isUAP

@[simp] lemma isUAP_comp_mulEquiv {φ : H ≃* G} : IsUAP (f ∘ φ) ↔ IsUAP f := by
  simp [isUAP_iff_exists_isUAPWith]

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

/-- Almost periodicity is preserved by uniform limits along any (nontrivial) filter. -/
lemma IsUAP.of_tendstoUniformly {ι : Type*} {p : Filter ι} [p.NeBot] {u : ι → G → E}
    (hu : ∀ᶠ n in p, IsUAP (u n)) (h : TendstoUniformly u f p) : IsUAP f := by
  intro ε hε
  obtain ⟨n, hn, hu⟩ := ((Metric.tendstoUniformly_iff.1 h (ε / 3) (by positivity)).and hu).exists
  obtain ⟨K, hu⟩ := hu (ε := ε / 3) (by positivity)
  refine ⟨K, hu.subset_right ?_⟩
  convert uniformAP_subset_of_forall_norm_sub_le (f := f) fun x ↦ by
    simpa [dist_eq_norm] using (hn x).le
  ring

lemma IsUAP.comp_mul_right (hf : IsUAP f) : IsUAP (fun x ↦ f (x * a)) := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith; exact hf.comp_mul_right.isUAP

lemma IsUAP.comp_mul_left (hf : IsUAP f) : IsUAP (fun x ↦ f (a * x)) := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith; exact hf.comp_mul_left.isUAP

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

@[fun_prop] protected lemma IsUAP.translate (hf : IsUAP f) : IsUAP (τ_[x] f) := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith; exact hf.translate.isUAP

@[simp] lemma isUAP_translate : IsUAP (τ_[x] f) ↔ IsUAP f where
  mp hf := by simpa using hf.translate (x := x⁻¹)
  mpr := .translate

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

section NormedCommRing
variable [NormedCommRing R] [StarRing R] [NormedStarGroup R] {f : G → R}

open scoped ComplexConjugate in
protected lemma IsUAP.conj (hf : IsUAP f) : IsUAP fun x ↦ conj (f x) := hf.star

end NormedCommRing
