module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.Additive.CovBySMul

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Group
import MeanFourier.Mathlib.Data.Fintype.BigOperators

open scoped Finset Pointwise

public section

variable {G X : Type*} [Group G] [MulAction G X] {A B : Set X} {K L : ℝ} {m n : ℕ}

namespace CovBySMul

attribute [gcongr] CovBySMul.subset_left CovBySMul.subset_right

@[to_additive]
lemma prod {H : Type*} [Group H] {A B : Set G} {C D : Set H} (hAB : CovBySMul G K A B)
    (hCD : CovBySMul H L C D) : CovBySMul (G × H) (K * L) (A ×ˢ C) (B ×ˢ D) := by
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

@[to_additive]
lemma univ_inter {A B : Set G} {K' L' : ℝ}
    (hA : CovBySMul G K' .univ A) (hB : CovBySMul G L' .univ B) :
    CovBySMul G (K' * L') .univ (A⁻¹ * A ∩ (B⁻¹ * B)) := by
  classical
  obtain ⟨F₁, hF₁card, hF₁⟩ := hA
  obtain ⟨F₂, hF₂card, hF₂⟩ := hB
  have (x : G) : ∃ p : G × G, p.1 ∈ F₁ ∧ p.2 ∈ F₂ ∧ p.1⁻¹ * x ∈ A ∧ p.2⁻¹ * x ∈ B := by
    obtain ⟨s, hs, a, ha, hsa⟩ := hF₁ (Set.mem_univ x)
    obtain ⟨u, hu, b, hb, hub⟩ := hF₂ (Set.mem_univ x)
    dsimp only at hsa hub
    rw [smul_eq_mul] at hsa hub
    have : s⁻¹ * x = a := by rw [← hsa]; group
    have : u⁻¹ * x = b := by rw [← hub]; group
    have hA' : s⁻¹ * x ∈ A := by grind
    have hB' : u⁻¹ * x ∈ B := by grind
    exact ⟨(s, u), hs, hu, hA', hB'⟩
  choose pair hp1 hp2 hpA hpB using this
  let rep := fun p ↦ if h : ∃ y, pair y = p then h.choose else 1
  have (x : G) : pair (rep (pair x)) = pair x := by
    have : ∃ y, pair y = pair x := ⟨x, by rfl⟩
    grind
  refine ⟨(F₁ ×ˢ F₂).image rep, ?_, ?_⟩
  · have : 0 ≤ K' := le_trans (by grind) hF₁card
    calc (((F₁ ×ˢ F₂).image rep).card : ℝ)
        ≤ (F₁ ×ˢ F₂).card := by exact_mod_cast Finset.card_image_le
      _ = F₁.card * F₂.card := by simp
      _ ≤ K' * L' := mul_le_mul hF₁card hF₂card (by grind) this
  · intro x _
    let r := rep (pair x)
    refine Set.mem_smul.2 ⟨r, ?_, r⁻¹ * x, ?_, by simp⟩
    · exact Finset.mem_image.2 ⟨pair x, Finset.mem_product.2 ⟨hp1 x, hp2 x⟩, by rfl⟩
    · exact ⟨
        ⟨((pair x).1⁻¹ * r)⁻¹, by grind [Set.mem_inv, inv_inv], (pair x).1⁻¹ * x, hpA x, by group⟩,
        ⟨((pair x).2⁻¹ * r)⁻¹, by grind [Set.mem_inv, inv_inv], (pair x).2⁻¹ * x, hpB x, by group⟩
      ⟩

end CovBySMul
