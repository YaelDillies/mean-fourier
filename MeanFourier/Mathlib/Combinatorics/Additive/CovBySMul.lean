module

public import Mathlib.Combinatorics.Additive.CovBySMul
public import Mathlib.Topology.MetricSpace.CoveringNumbers

import Mathlib.Tactic.Group
import MeanFourier.Mathlib.Data.EReal.Basic

open Metric
open scoped Finset Pointwise NNReal ENNReal

public section

variable {G X : Type*} [Group G]

section PseudoMetricSpace
variable [PseudoMetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] {K : ℝ} {ε : ℝ}

lemma smul_closedBall_eq_univ_iff_isCover (hε : 0 ≤ ε) (x₀ : G) {F : Set G} :
    F • closedBall x₀ ε = .univ ↔ IsCover ε.toNNReal .univ F⁻¹ := by
  refine ⟨fun h x _ ↦ ?_, fun h ↦ ?_⟩
  · have h_sub : Set.univ ⊆ F • closedBall x₀ ε := h.symm.subset
    obtain ⟨g, hg, y, hy, hxy⟩ := Set.mem_smul.mp (h_sub (Set.mem_univ (x⁻¹ * x₀)))
    refine ⟨g⁻¹, by simp [hg], ?_⟩
    simp only [Set.mem_ofPred_eq]
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
    simp only [Set.mem_ofPred_eq] at hdist
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
