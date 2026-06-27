module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.Additive.CovBySMul
public import Mathlib.Topology.MetricSpace.CoveringNumbers

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Group
import MeanFourier.Mathlib.Data.Fintype.BigOperators

open Metric
open scoped Finset Pointwise NNReal ENNReal

public section

variable {M G X : Type*}


namespace CovBySMul
section Monoid
variable [Monoid M] [MulAction M X] {A B : Set X} {K L ε : ℝ} {m n : ℕ}

attribute [gcongr] CovBySMul.subset_left CovBySMul.subset_right

@[to_additive]
lemma prod {N : Type*} [Group N] {A B : Set M} {C D : Set N} (hAB : CovBySMul M K A B)
    (hCD : CovBySMul N L C D) : CovBySMul (M × N) (K * L) (A ×ˢ C) (B ×ˢ D) := by
  obtain ⟨F₁, h₁, hAB⟩ := hAB
  obtain ⟨F₂, h₂, hCD⟩ := hCD
  classical
  refine ⟨F₁ ×ˢ F₂, ?_, ?_⟩
  · simp only [Finset.card_product, Nat.cast_mul]
    gcongr
    grw [← h₁]
    positivity
  rintro ⟨x, y⟩ ⟨(hx : x ∈ _), hy⟩
  obtain ⟨g, hg, b, hb, rfl⟩ := hAB hx
  obtain ⟨h, hh, d, hd, rfl⟩ := hCD hy
  exact ⟨(g, h), by simp [*], (b, d), by simp [*]⟩

@[to_additive]
lemma pi {ι : Type*} {G X : ι → Type*} {s : Finset ι} [∀ i, Group (G i)]
    [∀ i, MulAction (G i) (X i)] {A B : ∀ i, Set (X i)} {K : ι → ℝ}
    (hAB : ∀ i ∈ s, CovBySMul (G i) (K i) (A i) (B i)) :
    CovBySMul (∀ i, G i) (∏ i ∈ s, K i) (.pi s A) (.pi s B) := by
  choose! F hF hFS using hAB
  classical
  refine ⟨.pi' s (fun i ↦ if i ∈ s then F i else {1}) <| by simp +contextual, ?_, fun x hx ↦ ?_⟩
  · simp +contextual only [↓reduceIte, Finset.singleton_inj, exists_eq', implies_true,
      Finset.card_pi', Nat.cast_prod]
    gcongr with i hi
    exact hF _ hi
  have (i : ι) : Nonempty (X i) := ⟨x i⟩
  choose! g hg y hy hgy using fun i hi ↦ hFS i hi <| hx _ hi
  exact ⟨fun i ↦ if i ∈ s then g i else 1, by simp_all [apply_ite],
    fun i ↦ if i ∈ s then y i else x i, by simp_all, by ext; dsimp; split <;> simp_all⟩

variable [PseudoMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M]

@[simp]
lemma covBySMul_univ_ball_one :
    CovBySMul M K .univ (ball (1 : M) ε) ↔
      (coveringNumber ε.toNNReal (.univ : Set M) : EReal) ≤ K := by
  sorry

end Monoid

variable [Group G]

@[to_additive]
lemma inter {A B C : Set G} {K' L' : ℝ} (hA : CovBySMul G K' C A) (hB : CovBySMul G L' C B) :
    CovBySMul G (K' * L') C (A⁻¹ * A ∩ (B⁻¹ * B)) := by
  classical
  obtain ⟨F₁, hF₁card, hF₁⟩ := hA
  obtain ⟨F₂, hF₂card, hF₂⟩ := hB
  have (x : G) (hx : x ∈ C) : ∃ p : G × G, p.1 ∈ F₁ ∧ p.2 ∈ F₂ ∧ p.1⁻¹ * x ∈ A ∧ p.2⁻¹ * x ∈ B := by
    obtain ⟨s, hs, a, ha, hsa⟩ := hF₁ hx
    obtain ⟨u, hu, b, hb, hub⟩ := hF₂ hx
    exact ⟨(s, u), by grind [smul_eq_mul, inv_mul_cancel_left]⟩
  choose! pair hp using this
  let rep (p : G × G) : G := if h : ∃ y ∈ C, pair y = p then h.choose else 1
  have (x : G) (hx : x ∈ C) : pair (rep (pair x)) = pair x := by
    have : ∃ y ∈ C, pair y = pair x := ⟨x, hx, by rfl⟩
    grind
  refine ⟨(F₁ ×ˢ F₂).image rep, ?_, fun x hx ↦ ?_⟩
  · grw [Finset.card_image_le, Finset.card_product, Nat.cast_mul, hF₁card, hF₂card]
    grind
  · let r := rep (pair x)
    have : r ∈ C := by dsimp [r, rep]; split_ifs <;> grind
    refine ⟨r, by grind, r⁻¹ * x, ⟨
      ⟨((pair x).1⁻¹ * r)⁻¹, ?_, (pair x).1⁻¹ * x, (hp x hx).2.2.1, by group⟩,
      ⟨((pair x).2⁻¹ * r)⁻¹, ?_, (pair x).2⁻¹ * x, (hp x hx).2.2.2, by group⟩⟩, by simp⟩
      <;> grind [Set.mem_inv, inv_inv]

end CovBySMul
