/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Combinatorics.Additive.CovBySMul
public import MeanFourier.Mathlib.Combinatorics.Additive.CovBySMul
public import MeanFourier.Mathlib.Topology.Bornology.Basic
public import MeanFourier.AlmostConvergent

/-!
# Uniformly almost-periodic functions

This files defines uniformly almost-periodic functions in a group following von Neumann.

## References

* [*Almost periodic functions in a group. I*, John von Neumann](https://doi.org/10.2307/1989792)
-/

public section

open Bornology
open scoped Pointwise

variable {𝕜 G E : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {K L : ℝ → ℝ} {f g : G → E} {x t : G} {c : 𝕜} {z : E} {ε : ℝ}

variable (f ε) in
/-- The uniform `ε`-almost periods of a function `f` from a group `G` to a normed space `E` are
those elements of the group that move `f` by at most `ε` in L^∞ norm. -/
def uniformAP : Set G := {t | ∀ x, ‖f (t⁻¹ * x) - f x‖ ≤ ε}

@[inherit_doc uniformAP] notation3 "AP∞("f ", " ε ")" => uniformAP f ε

@[simp] lemma mem_uniformAP : t ∈ AP∞(f, ε) ↔ ∀ x, ‖f (t⁻¹ * x) - f x‖ ≤ ε := .rfl

@[to_fun (attr := simp) uniformAP_fun_const]
lemma uniformAP_const (hε : 0 ≤ ε) : AP∞(Function.const G z, ε) = .univ := by simp [uniformAP, hε]

@[to_fun (attr := simp) uniformAP_fun_smul]
lemma uniformAP_smul (hc : c ≠ 0) : AP∞(c • f, ε) = AP∞(f, ε / ‖c‖) := by
  ext t; simp [← smul_sub, norm_smul, le_div_iff₀' (norm_pos_iff.2 hc)]

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

@[simp]
lemma uniformAP_inv : (AP∞(f, ε))⁻¹ = AP∞(f, ε) := by
  ext t
  refine ⟨fun ht x ↦ ?_, fun ht x ↦ ?_⟩
  · specialize ht (t⁻¹ * x)
    simpa [norm_sub_rev] using ht
  · specialize ht (t * x)
    simpa [norm_sub_rev] using ht

lemma uniformAP_mul {a b : G} {δ : ℝ} (ha : a ∈ AP∞(f, ε)) (hb : b ∈ AP∞(f, δ)) :
    a * b ∈ AP∞(f, ε + δ) := by
  rw [mem_uniformAP] at ha hb ⊢
  intro x
  have : f ((a * b)⁻¹ * x) - f x
      = (f (b⁻¹ * (a⁻¹ * x)) - f (a⁻¹ * x)) + (f (a⁻¹ * x) - f x) := by
    grind [mul_inv_rev]
  grind [mul_inv_rev, norm_add_le]

lemma uniformAP_mul_uniformAP_subset {δ : ℝ} : AP∞(f, ε) * AP∞(f, δ) ⊆ AP∞(f, ε + δ) := by
  intro _ ⟨_, _, _, _, _⟩
  grind [uniformAP_mul]

lemma uniformAP_pow_subset (n : ℕ) : AP∞(f, ε) ^ n ⊆ AP∞(f, n • ε) := by
  induction n with
  | zero => simp [mem_uniformAP]
  | succ _ ih => exact (Set.mul_subset_mul_right ih).trans uniformAP_mul_uniformAP_subset

lemma inter_subset_uniformAP_add {δ : ℝ} :
    AP∞(f, ε) ∩ AP∞(g, δ) ⊆ AP∞(f + g, ε + δ) := by
  intro t ht
  obtain ⟨htf, htg⟩ := ht
  rw [mem_uniformAP]
  intro x
  simp only [Pi.add_apply]
  have h1 : f (t⁻¹ * x) + g (t⁻¹ * x) - (f x + g x)
      = (f (t⁻¹ * x) - f x) + (g (t⁻¹ * x) - g x) := by grind
  rw [h1]
  refine (norm_add_le _ _).trans ?_
  grw [htf x, htg x]

protected lemma IsUAPWith.add (hf : IsUAPWith K f) (hg : IsUAPWith L g) :
    IsUAPWith (fun ε ↦ K (ε / 4) * L (ε / 4)) (f + g) := by
  rintro ε hε
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  refine (CovBySMul.univ_inter (hf hε4) (hg hε4)).subset_right ?_
  calc
    (AP∞(f, ε / 4))⁻¹ * AP∞(f, ε / 4) ∩ ((AP∞(g, ε / 4))⁻¹ * AP∞(g, ε / 4))
        ⊆ AP∞(f, ε / 2) ∩ AP∞(g, ε / 2) := by
      have hhalf : ε / 4 + ε / 4 = ε / 2 := by ring
      gcongr <;>
      · rw [uniformAP_inv]
        rw [← hhalf]
        exact uniformAP_mul_uniformAP_subset
    _ ⊆ AP∞(f + g, ε) := by
      have := inter_subset_uniformAP_add (f := f) (g := g) (ε := ε / 2) (δ := ε / 2)
      simp_all

@[to_fun]
protected lemma IsUAPWith.smul (hf : IsUAPWith K f) (hc : c ≠ 0) :
    IsUAPWith (fun ε ↦ K <| ε / ‖c‖) (c • f) := by
  rintro ε hε
  simp only [ne_eq, hc, not_false_eq_true, uniformAP_smul]
  exact hf <| by positivity

@[fun_prop]
protected lemma IsUAPWith.translate (hf : IsUAPWith K f) : IsUAPWith K (τ_[t] f) := by
  simpa [IsUAPWith] using hf

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

@[fun_prop]
protected lemma IsUAP.translate (hf : IsUAP f) : IsUAP (τ_[x] f) := by
  obtain ⟨K, hf⟩ := hf.exists_isUAPWith; exact hf.translate.isUAP

@[fun_prop]
protected lemma IsUAP.isBddFun (hf : IsUAP f) : IsBddFun f := by
  sorry

@[fun_prop]
protected lemma IsUAP.isAlmostConvergent [NormedSpace ℝ E] (hf : IsUAP f) :
    IsAlmostConvergent f := by
  sorry
