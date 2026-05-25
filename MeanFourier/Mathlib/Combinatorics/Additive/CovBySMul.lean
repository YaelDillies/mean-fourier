module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.Additive.CovBySMul

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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

end CovBySMul
