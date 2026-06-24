/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Combinatorics.Additive.CovBySMul
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

lemma uniformAP_inv_subset : (AP∞(f, ε))⁻¹ ⊆ AP∞(f, ε) := by
  intro t ht
  rw [Set.mem_inv, mem_uniformAP] at ht
  rw [mem_uniformAP]
  intro x
  have := ht (t⁻¹ * x)
  simp only [inv_inv, mul_inv_cancel_left] at this
  rw [norm_sub_rev]
  exact this

lemma uniformAP_mul_subset {δ : ℝ} : AP∞(f, ε) * AP∞(f, δ) ⊆ AP∞(f, ε + δ) := by
  rw [Set.mul_subset_iff]
  intro a ha b hb x
  have : f ((a * b)⁻¹ * x) - f x
      = (f (b⁻¹ * (a⁻¹ * x)) - f (a⁻¹ * x)) + (f (a⁻¹ * x) - f x) := by
    rw [mul_inv_rev, mul_assoc]
    grind
  rw [this]
  calc ‖(f (b⁻¹ * (a⁻¹ * x)) - f (a⁻¹ * x)) + (f (a⁻¹ * x) - f x)‖
      ≤ ‖f (b⁻¹ * (a⁻¹ * x)) - f (a⁻¹ * x)‖ + ‖f (a⁻¹ * x) - f x‖ := norm_add_le _ _
    _ ≤ δ + ε := add_le_add (hb (a⁻¹ * x)) (ha x)
    _ = ε + δ := by group

lemma uniformAP_add_inter_subset {δ : ℝ} :
    AP∞(f, ε) ∩ AP∞(g, δ) ⊆ AP∞(f + g, ε + δ) := by
  intro t ht
  obtain ⟨htf, htg⟩ := ht
  rw [mem_uniformAP]
  intro x
  simp only [Pi.add_apply]
  calc ‖f (t⁻¹ * x) + g (t⁻¹ * x) - (f x + g x)‖
      = ‖(f (t⁻¹ * x) - f x) + (g (t⁻¹ * x) - g x)‖ := by congr; grind
    _ ≤ ‖f (t⁻¹ * x) - f x‖ + ‖g (t⁻¹ * x) - g x‖ := norm_add_le _ _
    _ ≤ ε + δ := add_le_add (htf x) (htg x)

lemma covBySMul_inter_of_univ {A B : Set G} {K' L' : ℝ}
    (hA : CovBySMul G K' Set.univ A) (hB : CovBySMul G L' Set.univ B) :
    CovBySMul G (K' * L') Set.univ (A⁻¹ * A ∩ (B⁻¹ * B)) := by
  classical
  obtain ⟨F₁, hF₁card, hF₁⟩ := hA
  obtain ⟨F₂, hF₂card, hF₂⟩ := hB
  have hcoord : ∀ x : G, ∃ p : G × G,
      p.1 ∈ F₁ ∧ p.2 ∈ F₂ ∧ p.1⁻¹ * x ∈ A ∧ p.2⁻¹ * x ∈ B := by
    intro x
    obtain ⟨s, hs, a, ha, hsa⟩ := Set.mem_smul.1 (hF₁ (Set.mem_univ x))
    obtain ⟨u, hu, b, hb, hub⟩ := Set.mem_smul.1 (hF₂ (Set.mem_univ x))
    rw [smul_eq_mul] at hsa hub
    have : s⁻¹ * x = a := by rw [← hsa]; group
    have : u⁻¹ * x = b := by rw [← hub]; group
    have hA' : s⁻¹ * x ∈ A := by simp_all
    have hB' : u⁻¹ * x ∈ B := by simp_all
    exact ⟨(s, u), hs, hu, hA', hB'⟩
  choose pair hp1 hp2 hpA hpB using hcoord
  let rep := fun p ↦ if h : ∃ y, pair y = p then h.choose else 1
  have : ∀ x, pair (rep (pair x)) = pair x := by
    intro x
    have : ∃ y, pair y = pair x := ⟨x, rfl⟩
    grind
  refine ⟨(F₁ ×ˢ F₂).image rep, ?_, ?_⟩
  · have : (0 : ℝ) ≤ K' := le_trans (by positivity) hF₁card
    calc (((F₁ ×ˢ F₂).image rep).card : ℝ)
        ≤ ((F₁ ×ˢ F₂).card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ = (F₁.card : ℝ) * (F₂.card : ℝ) := by simp
      _ ≤ K' * L' := mul_le_mul hF₁card hF₂card (by positivity) this
  · intro x _
    let r := rep (pair x)
    refine Set.mem_smul.2 ⟨r, ?_, r⁻¹ * x, ?_, by simp⟩
    · grind
    · refine ⟨?_, ?_⟩
      · rw [Set.mem_mul]
        refine ⟨((pair x).1⁻¹ * r)⁻¹, ?_, (pair x).1⁻¹ * x, hpA x, by group⟩
        rw [Set.mem_inv, inv_inv]
        grind
      · rw [Set.mem_mul]
        refine ⟨((pair x).2⁻¹ * r)⁻¹, ?_, (pair x).2⁻¹ * x, hpB x, by group⟩
        rw [Set.mem_inv, inv_inv]
        grind

theorem IsUAPWith.add :
    ∃ M, ∀ f : G → E, IsUAPWith K f → ∀ g, IsUAPWith L g → IsUAPWith M (f + g) := by
  refine ⟨fun ε ↦ K (ε / 4) * L (ε / 4), fun f hf g hg ε hε ↦ ?_⟩
  have : (0 : ℝ) < ε / 4 := by grind
  refine (covBySMul_inter_of_univ (hf this) (hg this)).subset_right ?_
  calc
    (AP∞(f, ε / 4))⁻¹ * AP∞(f, ε / 4) ∩ ((AP∞(g, ε / 4))⁻¹ * AP∞(g, ε / 4))
        ⊆ AP∞(f, ε / 2) ∩ AP∞(g, ε / 2) := by
      have : ε / 4 + ε / 4 = ε / 2 := by group
      gcongr <;>
      · refine (Set.mul_subset_mul_right uniformAP_inv_subset).trans ?_
        rw [← this]
        exact uniformAP_mul_subset
    _ ⊆ AP∞(f + g, ε) := by
      have := uniformAP_add_inter_subset (f := f) (g := g) (ε := ε / 2) (δ := ε / 2)
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
  obtain ⟨_, hf⟩ := hf.exists_isUAPWith
  obtain ⟨_, hg⟩ := hg.exists_isUAPWith
  obtain ⟨_, h⟩ := IsUAPWith.add (G := G) (E := E)
  exact (h _ hf _ hg).isUAP

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
