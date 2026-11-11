module

public import Mathlib.Combinatorics.Additive.CovBySMul
public import Mathlib.Topology.MetricSpace.CoveringNumbers

import AddCombi.Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Card

public section

open Metric
open scoped Finset Pointwise NNReal ENNReal

variable {G X : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] {K : ℝ} {ε : ℝ}

lemma smul_closedBall_eq_univ_iff_isCover (hε : 0 ≤ ε) (x₀ : G) {F : Set G} :
    F • closedBall x₀ ε = .univ ↔ IsCover ε.toNNReal .univ F⁻¹ := by
  have (g y : G) : dist (g⁻¹ * y) x₀ = dist (x₀ * y⁻¹) g⁻¹ := by
    rw [dist_comm, ← dist_mul_right _ _ y⁻¹, mul_inv_cancel_right]
  simp only [IsCover, SetRel.IsCover, Set.eq_univ_iff_forall, Set.mem_univ, true_imp_iff,
    Set.mem_smul_iff_inv_smul_mem]
  refine ((Equiv.inv G).trans (.mulLeft x₀)).forall_congr fun y ↦ ?_
  simp [this, Real.le_toNNReal_iff_coe_le hε]

@[simp]
lemma covBySMul_univ_closedBall_iff (hε : 0 ≤ ε) (x₀ : G) :
    CovBySMul G K .univ (closedBall x₀ ε) ↔
      (coveringNumber ε.toNNReal (.univ : Set G) : EReal) ≤ K := by
  classical
  simp_rw [CovBySMul, Set.univ_subset_iff, smul_closedBall_eq_univ_iff_isCover hε]
  refine ⟨fun ⟨F, hF, hFcov⟩ ↦ ?_, fun h ↦ ?_⟩
  · have := hFcov.coveringNumber_le_encard (Set.subset_univ _)
    rw [Set.encard_inv, Set.encard_coe_eq_coe_finsetCard] at this
    exact (mod_cast this : (_ : EReal) ≤ (#F : ℕ∞)).trans (EReal.coe_le_coe_iff.2 hF)
  · obtain ⟨C, -, hCfin, hC, hCcard⟩ :=
      exists_set_encard_eq_coveringNumber (ε := ε.toNNReal) (A := .univ) fun h' ↦ by
        rw [h'] at h; simp at h
    rw [← hCcard, ← hCfin.coe_toFinset, Set.encard_coe_eq_coe_finsetCard] at h
    exact ⟨hCfin.toFinset⁻¹, by simpa using EReal.coe_le_coe_iff.1 h, by simpa using hC⟩
