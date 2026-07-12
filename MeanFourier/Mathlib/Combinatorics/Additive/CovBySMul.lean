module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.Additive.CovBySMul
public import Mathlib.Topology.MetricSpace.CoveringNumbers

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Group
import MeanFourier.Mathlib.Data.EReal.Basic
import MeanFourier.Mathlib.Data.Fintype.BigOperators

/-!
## TODO

Protected `CovBySMul.rfl`
-/

open Metric
open scoped Finset Pointwise NNReal ENNReal

public section

variable {M G X : Type*}

section Monoid
variable [Monoid M] [MulAction M X] {A B : Set X} {K L ε : ℝ} {m n : ℕ}

attribute [gcongr] CovBySMul.subset_left CovBySMul.subset_right

@[to_additive]
lemma CovBySMul.pos (hAB : CovBySMul M K A B) (hA : A.Nonempty) : 0 < K := by
  obtain ⟨F, hFK, hFAB⟩ := hAB; contrapose! hA; grw [hA] at hFK; simp_all

@[to_additive]
lemma CovBySMul.prod {N : Type*} [Group N] {A B : Set M} {C D : Set N} (hAB : CovBySMul M K A B)
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
lemma CovBySMul.pi {ι : Type*} {G X : ι → Type*} {s : Finset ι} [∀ i, Group (G i)]
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

end Monoid

variable [Group G] {A B C : Set G} {K L : ℝ}

@[to_additive]
lemma CovBySMul.inter (hA : CovBySMul G K C A) (hB : CovBySMul G L C B) :
    CovBySMul G (K * L) C (A⁻¹ * A ∩ (B⁻¹ * B)) := by
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

/-- Covering `B` by `K` right translates of `A` is the same as covering `B⁻¹` by `K` left translates
of `A⁻¹`. -/
lemma covBySMul_mulOpposite_iff : CovBySMul Gᵐᵒᵖ K A B ↔ CovBySMul G K A⁻¹ B⁻¹ := by
  refine ((Equiv.inv G).trans MulOpposite.opEquiv).finsetCongr.symm.exists_congr' ?_
  simp [Set.inv_subset, ← Function.comp_def _ (·⁻¹), Set.image_comp, -MulOpposite.op_inv,
    Set.image_op_smul]

section PseudoMetricSpace
variable [PseudoMetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] {K L : ℝ} {ε : ℝ}

lemma smul_closedBall_eq_univ_iff_isCover (hε : 0 ≤ ε) (x₀ : G) {F : Set G} :
    F • closedBall x₀ ε = .univ ↔ IsCover ε.toNNReal .univ F⁻¹ := by
  refine ⟨fun h x _ ↦ ?_, fun h ↦ ?_⟩
  · have h_sub : Set.univ ⊆ F • closedBall x₀ ε := h.symm.subset
    obtain ⟨g, hg, y, hy, hxy⟩ := Set.mem_smul.mp (h_sub (Set.mem_univ (x⁻¹ * x₀)))
    refine ⟨g⁻¹, by simp [hg], ?_⟩
    simp only [Set.mem_setOf_eq]
    have hxy' : g⁻¹ * x⁻¹ * x₀ = y := by rw [mul_assoc, ← hxy, smul_eq_mul, inv_mul_cancel_left]
    rw [edist_le_coe, ← dist_le_coe, Real.coe_toNNReal _ hε]
    rw [mem_closedBall] at hy
    rw [← hxy'] at hy
    have : dist (g⁻¹ * x⁻¹ * x₀) x₀ = dist g⁻¹ x := by
      have h_dist := dist_mul_right (g⁻¹ * x⁻¹) 1 x₀
      rw [one_mul] at h_dist
      have h1 : dist (g⁻¹ * x⁻¹) 1 = dist (g⁻¹ * x⁻¹ * x) (1 * x) :=
        (dist_mul_right _ _ _).symm
      rw [one_mul] at h1
      have h2 : g⁻¹ * x⁻¹ * x = g⁻¹ := by group
      rw [h2] at h1
      rw [h_dist, h1]
    rwa [this, dist_comm] at hy
  · rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨g_inv, hg_inv, hdist⟩ := h (Set.mem_univ (x₀ * x⁻¹))
    refine ⟨g_inv⁻¹, hg_inv, g_inv * x, ?_, by simp⟩
    rw [mem_closedBall]
    have h_eq : dist (g_inv * x) x₀ = dist g_inv (x₀ * x⁻¹) := by
      have h1 : dist g_inv (x₀ * x⁻¹) = dist (g_inv * x) (x₀ * x⁻¹ * x) :=
        (dist_mul_right _ _ _).symm
      have h2 : x₀ * x⁻¹ * x = x₀ := by group
      rw [h2] at h1
      exact h1.symm
    rw [h_eq, dist_comm]
    simp only [Set.mem_setOf_eq] at hdist
    rwa [edist_le_coe, ← dist_le_coe, Real.coe_toNNReal _ hε] at hdist

@[simp]
lemma univ_closedBall (hε : 0 ≤ ε) (x₀ : G) :
    CovBySMul G K .univ (closedBall x₀ ε) ↔
      (coveringNumber ε.toNNReal (.univ : Set G) : EReal) ≤ K := by
  classical
  refine ⟨?_, ?_⟩
  · rintro ⟨F, hF, h_cover⟩
    rw [Set.univ_subset_iff] at h_cover
    rw [smul_closedBall_eq_univ_iff_isCover hε x₀] at h_cover
    have h_card : ((F : Set G)⁻¹).encard = F.card := by
      rw [← Set.inv_preimage, Set.encard_preimage_of_bijective inv_bijective,
        Set.encard_coe_eq_coe_finsetCard]
    have h_le : (coveringNumber ε.toNNReal (.univ : Set G) : EReal) ≤ ((F.card : ℕ∞) : EReal) := by
      exact_mod_cast h_card ▸ h_cover.coveringNumber_le_encard (Set.subset_univ _)
    have hF_cast : ((F.card : ℕ∞) : EReal) ≤ K := by
      change (F.card : EReal) ≤ K
      exact_mod_cast hF
    exact h_le.trans hF_cast
  · intro h
    have h_ne_top : coveringNumber ε.toNNReal (.univ : Set G) ≠ ⊤ :=
      ENat.ne_top_of_ennrealToEReal_toENNReal_le_realToEReal h
    set F' : Finset G := (finite_minimalCover (A := (.univ : Set G)) (ε := ε.toNNReal)).toFinset
    have hF'_card_top : (F'.card : ℕ∞) = coveringNumber ε.toNNReal (.univ : Set G) := by
      rw [← Set.encard_coe_eq_coe_finsetCard, Set.Finite.coe_toFinset, encard_minimalCover h_ne_top]
    have h_cover : IsCover ε.toNNReal (.univ : Set G) (F' : Set G) := by
      rw [Set.Finite.coe_toFinset]
      exact isCover_minimalCover h_ne_top
    refine ⟨F'.image (·⁻¹), ?_, ?_⟩
    · rw [Finset.card_image_of_injective F' inv_injective]
      have : F'.card = (coveringNumber ε.toNNReal (.univ : Set G)).toNat :=
        congrArg ENat.toNat hF'_card_top
      rw [this]
      exact ENat.natCast_toNat_le_of_ennrealToEReal_toENNReal_le_realToEReal h
    · rw [Set.univ_subset_iff, smul_closedBall_eq_univ_iff_isCover hε x₀]
      have : ((F'.image (fun x ↦ x⁻¹ : G → G) : Set G)⁻¹) = (F' : Set G) := by simp
      exact this.symm ▸ h_cover

@[simp]
lemma univ_closedBall_one (hε : 0 ≤ ε) :
    CovBySMul G K .univ (closedBall (1 : G) ε) ↔
      (coveringNumber ε.toNNReal (.univ : Set G) : EReal) ≤ K :=
  univ_closedBall hε 1

end PseudoMetricSpace
