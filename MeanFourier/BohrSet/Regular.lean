/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import MeanFourier.BohrSet.Defs
public import MeanFourier.Mathlib.Topology.MetricSpace.CoveringNumbers

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Regular Bohr sets
-/

public section

open AddChar Complex Function MeasureTheory Metric Module
open scoped NNReal Pointwise

namespace BohrSet

lemma norm_sub_le_of_norm_sub_le_div_two {E : Type*} [NormedAddCommGroup E] {a b c : E} {r : ℝ}
    (ha : ‖a - c‖ ≤ r / 2) (hb : ‖b - c‖ ≤ r / 2) : ‖a - b‖ ≤ r := by
  have : ‖a - b‖ ≤ ‖a - c‖ + ‖c - b‖ := norm_sub_le_norm_sub_add_norm_sub a c b
  have : ‖c - b‖ = ‖b - c‖ := norm_sub_rev c b
  linarith

lemma closedBall_ratio_le {ρ w : ℝ} (hρ : 0 < ρ) (hρ_le : ρ ≤ 1) (hw : 0 < w) {r : ℝ}
    (hr_eq : r = ρ * w / 2) : (2 * w + r) / r ≤ 5 / ρ := by
  have : 0 < r := by
    rw [hr_eq]
    positivity
  rw [div_le_div_iff₀ this hρ, hr_eq]
  nlinarith

lemma nat_mul_div_self_add_one_le (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    (n : ℝ) * (ε / (n + 1)) ≤ ε := by
  rw [← mul_div_assoc]
  have h_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine div_le_iff₀ h_pos |>.mpr ?_
  nlinarith

lemma lt_of_mul_exp_lt {a b K δ : ℝ} (ha : 0 ≤ a) (hKδ : 0 ≤ K * δ)
    (h : a * Real.exp (K * δ) < b) : a < b := by
  have : a ≤ a * Real.exp (K * δ) :=
    le_mul_of_one_le_right ha (Real.one_le_exp hKδ)
  exact this.trans_lt h

lemma neg_log_one_sub_le_div {κ : ℝ} (hκ₀ : 0 < κ) (hκ : κ ≤ 1 / 100) :
    -Real.log (1 - κ) ≤ (100 / 99) * κ := by
  have h_one_sub_κ : 0 < 1 - κ := by linarith
  have : -Real.log (1 - κ) ≤ (1 - κ)⁻¹ - 1 := by
    rw [← Real.log_inv]
    exact Real.log_le_sub_one_of_pos (inv_pos.mpr h_one_sub_κ)
  have : (1 - κ)⁻¹ - 1 = κ / (1 - κ) := by
    field_simp
    ring
  have : κ / (1 - κ) ≤ (100 / 99) * κ := by
    rw [div_le_iff₀ h_one_sub_κ]
    nlinarith [mul_le_mul_of_nonneg_left hκ hκ₀.le]
  linarith

variable {G : Type*} [Group G] {B : BohrSet G} {x : G} {ρ ε : ℝ}

/-- A Bohr set `B` is *regular* if the dilates of `B` by numbers close to `1` are of comparable size
to `B`. -/
structure IsRegular (B : BohrSet G) : Prop where
  le_natCard_smul (κ : ℝ) (hκ₀ : 0 ≤ κ) (hκ : κ ≤ (100 * B.dimSqRank : ℝ)⁻¹) :
    (1 - 100 * B.dimSqRank * κ) * Nat.card B ≤ Nat.card ↥((1 - κ) • B)
  natCard_smul_le (κ : ℝ) (hκ₀ : 0 ≤ κ) (hκ : κ ≤ (100 * B.dimSqRank : ℝ)⁻¹) :
    Nat.card ↥((1 + κ) • B) ≤ (1 + 100 * B.dimSqRank * κ) * Nat.card B

lemma exists_finset_cover (hρ : 0 < ρ) (hρ_le : ρ ≤ 1)
    (ψ : UnitaryDual ℂ G) (hψ : ψ ∈ B.frequencies) :
    ∃ s : Finset (ψ.E →L[ℂ] ψ.E),
      (s.card : ℝ) ≤ (5 / ρ) ^ (2 * finrank ℂ ψ.E ^ 2) ∧
      ∀ x ∈ (B : Set G), ∃ c ∈ s,
        ‖(ψ x : ψ.E →L[ℂ] ψ.E) - c‖ ≤ ρ * B.width ψ / 2 := by
  classical
  have : (1 : ℝ) ≤ (5 / ρ) ^ (2 * finrank ℂ ψ.E ^ 2) := by
    apply one_le_pow₀
    rw [le_div_iff₀ hρ]
    linarith
  obtain hw_eq | hw_ne := eq_or_ne (B.width ψ) 0
  · refine ⟨{1}, ?_, fun x hx ↦ ⟨1, Finset.mem_singleton_self _, ?_⟩⟩
    · rw [Finset.card_singleton, Nat.cast_one]
      exact this
    · have heq := mem_chordSet_iff_nnnorm_width.1 hx hψ
      rw [hw_eq, nonpos_iff_eq_zero, nnnorm_eq_zero, sub_eq_zero] at heq
      simp [← heq, hw_eq]
  · set w : ℝ≥0 := B.width ψ
    set r : ℝ≥0 := ρ.toNNReal * w / 2 with hr_def
    have hw : 0 < w := pos_of_ne_zero hw_ne
    have hr : 0 < r := by positivity
    have hr_eq : (r : ℝ) = ρ * w / 2 := by
      rw [hr_def]
      push_cast [Real.coe_toNNReal _ hρ.le]
      rfl
    set V : Set (ψ.E →L[ℂ] ψ.E) := closedBall 1 w with hV_def
    have : FiniteDimensional ℂ (ψ.E →L[ℂ] ψ.E) :=
      Module.Finite.equiv (LinearMap.toContinuousLinearMap : (ψ.E →ₗ[ℂ] ψ.E) ≃ₗ[ℂ] _)
    have : FiniteDimensional ℝ (ψ.E →L[ℂ] ψ.E) := .trans ℝ ℂ _
    have hcov := coveringNumber_closedBall_le (x := (1 : ψ.E →L[ℂ] ψ.E)) (R := (w : ℝ)) hr
      w.coe_nonneg
    have hne : coveringNumber r V ≠ ⊤ := (hcov.trans_lt (WithTop.coe_lt_top _)).ne
    have hfin : (minimalCover r V).Finite := by
      rw [← Set.encard_ne_top_iff, encard_minimalCover hne]
      exact hne
    refine ⟨hfin.toFinset, ?_, fun x hx ↦ ?_⟩
    · have h_card : (hfin.toFinset.card : ℕ∞) ≤
          (⌊((2 * (w : ℝ) + r) / r) ^ finrank ℝ (ψ.E →L[ℂ] ψ.E)⌋₊ : ℕ∞) := by
        rw [← hfin.encard_eq_coe_toFinset_card, encard_minimalCover hne]
        exact hcov
      have h_nonneg : 0 ≤ ((2 * (w : ℝ) + r) / r) ^ finrank ℝ (ψ.E →L[ℂ] ψ.E) := by positivity
      have : (hfin.toFinset.card : ℝ) ≤
          ((2 * (w : ℝ) + r) / r) ^ finrank ℝ (ψ.E →L[ℂ] ψ.E) :=
        (Nat.cast_le.2 (WithTop.coe_le_coe.1 h_card)).trans (Nat.floor_le h_nonneg)
      refine this.trans ?_
      rw [ψ.finrank_real_continuousLinearMap]
      have : 0 ≤ (2 * (w : ℝ) + r) / r := by positivity
      exact pow_le_pow_left₀ this
        (closedBall_ratio_le hρ hρ_le (NNReal.coe_pos.2 hw) hr_eq)
        (2 * finrank ℂ ψ.E ^ 2)
    · have : (ψ x : ψ.E →L[ℂ] ψ.E) ∈ V := by
        rw [hV_def, mem_closedBall, dist_eq_norm, norm_sub_rev]
        exact_mod_cast mem_chordSet_iff_nnnorm_width.1 hx hψ
      obtain ⟨c, hc, hdist⟩ := isCover_minimalCover hne this
      refine ⟨c, hfin.mem_toFinset.2 hc, ?_⟩
      simp only [Set.mem_setOf_eq] at hdist
      rw [edist_le_coe, ← NNReal.coe_le_coe, coe_nndist, dist_eq_norm] at hdist
      exact hdist.trans_eq hr_eq

lemma natCard_le_natCard_smul (hρ : 0 < ρ) (hρ_le : ρ ≤ 1) :
    (Nat.card B : ℝ) ≤ (5 / ρ) ^ (2 * B.dimSqRank) * Nat.card ↥(ρ • B) := by
  classical
  obtain hfin | hinf := (B : Set G).finite_or_infinite
  · have hsub : ((ρ • B : BohrSet G) : Set G) ⊆ (B : Set G) := by
      simpa using chordSet_smul_subset_smul_of_nonneg_right hρ.le hρ_le
    have hfin_ρ : ((ρ • B : BohrSet G) : Set G).Finite := hfin.subset hsub
    choose d hd_card hd_cover using
      fun ψ : ↥B.frequencies ↦ exists_finset_cover hρ hρ_le ψ.1 ψ.2
    set A : Finset G := hfin.toFinset
    choose! φ hφ_d hφ_dist using fun x (hx : x ∈ (B : Set G)) (ψ : ↥B.frequencies) ↦
      hd_cover ψ x hx
    set t := A.image φ
    have : t ⊆ Fintype.piFinset fun ψ ↦ d ψ := by
      intro y hy
      obtain ⟨x, hxA, rfl⟩ := Finset.mem_image.1 hy
      rw [Fintype.mem_piFinset]
      intro ψ
      exact hφ_d x (hfin.mem_toFinset.1 hxA) ψ
    have ht_card : (t.card : ℝ) ≤ (5 / ρ) ^ (2 * B.dimSqRank) := by
      calc (t.card : ℝ)
          ≤ ((Fintype.piFinset fun ψ ↦ d ψ).card : ℝ) :=
            Nat.cast_le.2 (Finset.card_le_card this)
        _ = ∏ ψ : ↥B.frequencies, ((d ψ).card : ℝ) := by simp
        _ ≤ ∏ ψ : ↥B.frequencies,
            (5 / ρ) ^ (2 * finrank ℂ (ψ : UnitaryDual ℂ G).E ^ 2) :=
            Finset.prod_le_prod (fun _ _ ↦ Nat.cast_nonneg _) fun ψ _ ↦ hd_card ψ
        _ = (5 / ρ) ^ ∑ ψ : ↥B.frequencies,
            2 * finrank ℂ (ψ : UnitaryDual ℂ G).E ^ 2 := by
            rw [← Finset.prod_pow_eq_pow_sum]
        _ = (5 / ρ) ^ (2 * B.dimSqRank) := by
            congr 1
            rw [dimSqRank_eq, Finset.mul_sum]
            exact Finset.sum_coe_sort B.frequencies
              (fun ψ ↦ 2 * finrank ℂ ψ.E ^ 2)
    have : A.card = ∑ y ∈ t, {x ∈ A | φ x = y}.card :=
      Finset.card_eq_sum_card_fiberwise fun x hx ↦ Finset.mem_image_of_mem φ hx
    obtain ⟨t₀, ht₀t, ht₀max⟩ := t.exists_max_image (fun y ↦ {x ∈ A | φ x = y}.card)
      (Finset.Nonempty.image ⟨1, hfin.mem_toFinset.2 one_mem_chordSet⟩ φ)
    set f₀ : Finset G := {x ∈ A | φ x = t₀}
    have hcount : A.card ≤ t.card * f₀.card := by
      rw [this]
      exact Finset.sum_le_card_nsmul t _ f₀.card fun y hy ↦ ht₀max y hy
    obtain ⟨x₀, hx₀A, hx₀φ⟩ := Finset.mem_image.1 ht₀t
    have hx₀B : x₀ ∈ (B : Set G) := hfin.mem_toFinset.1 hx₀A
    have hshift : ∀ y ∈ f₀, x₀⁻¹ * y ∈ ((ρ • B : BohrSet G) : Set G) := by
      intro y hyf
      have hyB : y ∈ (B : Set G) := hfin.mem_toFinset.1 (Finset.mem_filter.1 hyf).1
      have hyφ : φ y = t₀ := (Finset.mem_filter.1 hyf).2
      rw [mem_chordSet_iff_nnnorm_ewidth]
      intro ψ
      rw [ewidth_smul]
      by_cases hψ : ψ ∈ B.frequencies
      · rw [if_pos hψ, ← coe_width hψ, ← ENNReal.coe_mul, ENNReal.coe_le_coe,
          UnitaryDual.nnnorm_one_sub_map_inv_mul, ← NNReal.coe_le_coe]
        push_cast [Real.coe_nnabs, abs_of_nonneg hρ.le]
        have h₁ : ‖(ψ x₀ : ψ.E →L[ℂ] ψ.E) - t₀ ⟨ψ, hψ⟩‖ ≤ ρ * B.width ψ / 2 :=
          hx₀φ ▸ hφ_dist x₀ hx₀B ⟨ψ, hψ⟩
        have h₂ : ‖(ψ y : ψ.E →L[ℂ] ψ.E) - t₀ ⟨ψ, hψ⟩‖ ≤ ρ * B.width ψ / 2 :=
          hyφ ▸ hφ_dist y hyB ⟨ψ, hψ⟩
        exact norm_sub_le_of_norm_sub_le_div_two h₁ h₂
      · simp [hψ]
    have hcard_f₀ : f₀.card ≤ hfin_ρ.toFinset.card :=
      Finset.card_le_card_of_injOn (fun y ↦ x₀⁻¹ * y)
        (fun y hy ↦ hfin_ρ.mem_toFinset.2 (hshift y hy)) fun a _ b _ h ↦ mul_left_cancel h
    have hcard_eq : (Nat.card B : ℝ) = A.card := by
      rw [Nat.card_eq_card_finite_toFinset hfin]
    have hcard_smul : (Nat.card ↥(ρ • B) : ℝ) = hfin_ρ.toFinset.card := by
      rw [Nat.card_eq_card_finite_toFinset hfin_ρ]
    have hpos_pow : 0 ≤ (5 / ρ) ^ (2 * B.dimSqRank) := by positivity
    have : (A.card : ℝ) ≤ (t.card : ℝ) * f₀.card := by exact_mod_cast hcount
    calc (Nat.card B : ℝ) = A.card := hcard_eq
      _ ≤ (t.card : ℝ) * f₀.card := this
      _ ≤ (5 / ρ) ^ (2 * B.dimSqRank) * hfin_ρ.toFinset.card :=
          mul_le_mul ht_card (Nat.cast_le.2 hcard_f₀) (Nat.cast_nonneg _) hpos_pow
      _ = (5 / ρ) ^ (2 * B.dimSqRank) * Nat.card ↥(ρ • B) := by rw [← hcard_smul]
  · have : Infinite B := hinf.to_subtype
    simp only [Nat.card_eq_zero_of_infinite, Nat.cast_zero]
    positivity

lemma natCard_scale_le_natCard_scale {u v a δ₀ : ℝ} (huv : u ≤ v)
    (hgap : v - u ≤ a + δ₀) (hbase : 5 * Real.exp (a + δ₀) ≤ 8) :
    (Nat.card ↥((ε * Real.exp v) • B) : ℝ) ≤
      8 ^ (2 * B.dimSqRank) * Nat.card ↥((ε * Real.exp u) • B) := by
  have huv_le : Real.exp (u - v) ≤ 1 := Real.exp_le_one_iff.2 (sub_nonpos.2 huv)
  have : (Nat.card ↥((ε * Real.exp v) • B) : ℝ) ≤
      (5 / Real.exp (u - v)) ^ (2 * ((ε * Real.exp v) • B).dimSqRank) *
        Nat.card ↥(Real.exp (u - v) • (ε * Real.exp v) • B) :=
    natCard_le_natCard_smul (Real.exp_pos (u - v)) huv_le
  have h_scale : Real.exp (u - v) * (ε * Real.exp v) = ε * Real.exp u := by
    rw [mul_comm ε (Real.exp v), ← mul_assoc, ← Real.exp_add]
    ring_nf
  rw [dimSqRank_smul, smul_smul, h_scale] at this
  refine this.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · refine pow_le_pow_left₀ ?_ ?_ _
    · positivity
    · have : 5 / Real.exp (u - v) = 5 * Real.exp (v - u) := by
        rw [Real.exp_sub, Real.exp_sub]
        field_simp
      rw [this]
      have : Real.exp (v - u) ≤ Real.exp (a + δ₀) := Real.exp_le_exp.2 hgap
      have h5 : (0 : ℝ) ≤ 5 := by norm_num
      exact (mul_le_mul_of_nonneg_left this h5).trans hbase
  · simp [*]

lemma log_natCard_scale_sub_le {u v a δ₀ K : ℝ} (huv : u ≤ v)
    (hgap : v - u ≤ a + δ₀) (hbase : 5 * Real.exp (a + δ₀) ≤ 8)
    (hu_card : 1 ≤ Nat.card ↥((ε * Real.exp u) • B))
    (hv_card : 1 ≤ Nat.card ↥((ε * Real.exp v) • B))
    (hK : K = 60 * B.dimSqRank) (hK_pos : 0 < K) :
    (Real.log (Nat.card ↥((ε * Real.exp v) • B)) -
      Real.log (Nat.card ↥((ε * Real.exp u) • B))) / K ≤ Real.log 8 / 30 := by
  have hfu : (0 : ℝ) < Nat.card ↥((ε * Real.exp u) • B) := Nat.cast_pos.mpr hu_card
  have hfv : (0 : ℝ) < Nat.card ↥((ε * Real.exp v) • B) := Nat.cast_pos.mpr hv_card
  have : Real.log (Nat.card ↥((ε * Real.exp v) • B)) ≤
      2 * B.dimSqRank * Real.log 8 + Real.log (Nat.card ↥((ε * Real.exp u) • B)) := by
    have : (0 : ℝ) < 8 ^ (2 * B.dimSqRank) := by positivity
    have h_log : Real.log (8 ^ (2 * B.dimSqRank) * Nat.card ↥((ε * Real.exp u) • B)) =
        2 * B.dimSqRank * Real.log 8 + Real.log (Nat.card ↥((ε * Real.exp u) • B)) := by
      rw [Real.log_mul this.ne' hfu.ne', Real.log_pow]
      push_cast
      ring
    exact (Real.log_le_log hfv (natCard_scale_le_natCard_scale huv hgap hbase)).trans_eq h_log
  have : (0 : ℝ) < 30 := by norm_num
  rw [div_le_div_iff₀ hK_pos this, hK]
  have : Real.log 8 * (60 * B.dimSqRank) = 60 * (B.dimSqRank * Real.log 8) := by ring
  rw [this]
  linarith

lemma le_log_sub_log_of_mul_exp_le {K δ y z : ℝ} (hy : 0 < y) (h : y * Real.exp (K * δ) ≤ z) :
    K * δ ≤ Real.log z - Real.log y := by
  have : Real.log (y * Real.exp (K * δ)) ≤ Real.log z :=
    Real.log_le_log (mul_pos hy (Real.exp_pos _)) h
  rw [Real.log_mul hy.ne' (Real.exp_ne_zero _), Real.log_exp] at this
  linarith

lemma volume_bad_right_ineq (n : ℕ) {K δ a b c d η : ℝ} (hK : 0 < K) (hab : a ≤ b)
    (hδ : K * δ ≤ c - b) :
    (η + δ) + ((d - c) / K + n * η) ≤ (d - a) / K + (n + 1) * η := by
  have hδ_div : δ ≤ (c - b) / K := by
    rw [le_div_iff₀ hK, mul_comm]
    exact hδ
  have h_div_le : (d - b) / K ≤ (d - a) / K := by
    have : d - b ≤ d - a := by linarith
    exact div_le_div_of_nonneg_right this hK.le
  have h_sum : (c - b) / K + (d - c) / K = (d - b) / K := by ring
  linarith [hδ_div, h_div_le, h_sum]

lemma volume_bad_left_ineq (n : ℕ) {K δ a b c d η : ℝ} (hK : 0 < K) (hcd : c ≤ d)
    (hδ : K * δ ≤ c - b) :
    ((b - a) / K + n * η) + (δ + η) ≤ (d - a) / K + (n + 1) * η := by
  have hδ_div : δ ≤ (c - b) / K := by
    rw [le_div_iff₀ hK, mul_comm]
    exact hδ
  have h_div_le : (c - a) / K ≤ (d - a) / K := by
    have : c - a ≤ d - a := by linarith
    exact div_le_div_of_nonneg_right this hK.le
  have h_sum : (b - a) / K + (c - b) / K = (c - a) / K := by ring
  linarith [hδ_div, h_div_le, h_sum]

section ScaleSelection

private lemma volume_bad_right_le_aux {K δ₀ : ℝ} (hK : 0 < K) (hδ₀ : 0 < δ₀) (n : ℕ) :
    ∀ (f : ℝ → ℕ) (x₀ x₁ η : ℝ), 0 < η →
      MonotoneOn f (Set.Icc x₀ (x₁ + δ₀)) →
      (∀ u ∈ Set.Icc x₀ (x₁ + δ₀), 1 ≤ f u) →
      f (x₁ + δ₀) ≤ f x₀ + n →
      volume {u | u ∈ Set.Icc x₀ x₁ ∧ ∃ δ ∈ Set.Ioc (0 : ℝ) δ₀,
          (f u : ℝ) * Real.exp (K * δ) < f (u + δ)} ≤
        ENNReal.ofReal ((Real.log (f (x₁ + δ₀)) - Real.log (f x₀)) / K + n * η) := by
  induction n with
  | zero =>
    intro f x₀ x₁ η _hη hmono hpos _hbudget
    have : {u | u ∈ Set.Icc x₀ x₁ ∧ ∃ δ ∈ Set.Ioc (0 : ℝ) δ₀,
        (f u : ℝ) * Real.exp (K * δ) < f (u + δ)} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro u ⟨⟨hux₀, hux₁⟩, δ, ⟨hδ₁, hδ₂⟩, hlt⟩
      have hx₀ : x₀ ∈ Set.Icc x₀ (x₁ + δ₀) := ⟨le_rfl, by linarith⟩
      have hu : u ∈ Set.Icc x₀ (x₁ + δ₀) := ⟨hux₀, by linarith⟩
      have hu_δ_mem : u + δ ∈ Set.Icc x₀ (x₁ + δ₀) := ⟨by linarith, by linarith⟩
      have hx₁_δ₀_mem : x₁ + δ₀ ∈ Set.Icc x₀ (x₁ + δ₀) :=
          ⟨by linarith, le_rfl⟩
      have hu_δ_le : u + δ ≤ x₁ + δ₀ := by linarith
      have : f (u + δ) ≤ f (x₁ + δ₀) := hmono hu_δ_mem hx₁_δ₀_mem hu_δ_le
      have : f x₀ ≤ f u := hmono hx₀ hu hux₀
      have : f u < f (u + δ) := by
        exact_mod_cast lt_of_mul_exp_lt (Nat.cast_nonneg (f u))
          (mul_nonneg hK.le hδ₁.le) hlt
      lia
    simp_all
  | succ n ih =>
    intro f x₀ x₁ η hη hmono hpos hbudget
    set Bad := {u | u ∈ Set.Icc x₀ x₁ ∧ ∃ δ ∈ Set.Ioc (0 : ℝ) δ₀,
      (f u : ℝ) * Real.exp (K * δ) < f (u + δ)}
    rcases Set.eq_empty_or_nonempty Bad with he | hne
    · rw [he, measure_empty]
      simp
    · have : Bad ⊆ Set.Icc x₀ x₁ := fun v hv ↦ hv.1
      have hbdd : BddBelow Bad := bddBelow_Icc.mono this
      set ρ₀ := sInf Bad
      obtain ⟨u, ⟨⟨hux₀, hux₁⟩, δ, ⟨hδ₁, hδ₂⟩, hlt⟩, hu_lt⟩ :=
        (csInf_lt_iff hbdd hne).1 (lt_add_of_pos_right ρ₀ hη)
      have hx₀ : x₀ ∈ Set.Icc x₀ (x₁ + δ₀) := ⟨le_rfl, by linarith⟩
      have hu_mem : u ∈ Set.Icc x₀ (x₁ + δ₀) := ⟨hux₀, by linarith⟩
      have hu_δ_mem : u + δ ∈ Set.Icc x₀ (x₁ + δ₀) := ⟨by linarith, by linarith⟩
      have hfu : (0 : ℝ) < f u := Nat.cast_pos.mpr (hpos u hu_mem)
      have hfx₀ : (0 : ℝ) < f x₀ := Nat.cast_pos.mpr (hpos _ hx₀)
      have : f u < f (u + δ) := by
        exact_mod_cast lt_of_mul_exp_lt (Nat.cast_nonneg (f u)) (mul_nonneg hK.le hδ₁.le) hlt
      have hcover : Bad ⊆ Set.Icc ρ₀ (u + δ) ∪ {v | v ∈ Set.Icc (u + δ) x₁ ∧
          ∃ δ' ∈ Set.Ioc (0 : ℝ) δ₀, (f v : ℝ) * Real.exp (K * δ') < f (v + δ')} := by
        rintro v hv
        rcases le_or_gt v (u + δ) with hvu | hvu
        · exact Or.inl ⟨csInf_le hbdd hv, hvu⟩
        · exact Or.inr ⟨⟨hvu.le, hv.1.2⟩, hv.2⟩
      have hbudget_rec : f (x₁ + δ₀) ≤ f (u + δ) + n := by
        have : f x₀ ≤ f u := hmono hx₀ hu_mem hux₀
        lia
      have hrec := ih f (u + δ) x₁ η hη (hmono.mono (Set.Icc_subset_Icc hu_δ_mem.1 le_rfl))
        (fun v hv ↦ hpos v ⟨hu_δ_mem.1.trans hv.1, hv.2⟩) hbudget_rec
      have hx₁_δ₀_mem : x₁ + δ₀ ∈ Set.Icc x₀ (x₁ + δ₀) :=
        ⟨by linarith, le_rfl⟩
      have hfuδ : (0 : ℝ) < f (u + δ) := Nat.cast_pos.mpr (hpos _ hu_δ_mem)
      have hle : u + δ ≤ x₁ + δ₀ := by linarith
      have : Real.log (f (u + δ)) ≤ Real.log (f (x₁ + δ₀)) :=
        Real.log_le_log hfuδ (Nat.cast_le.mpr (hmono hu_δ_mem hx₁_δ₀_mem hle))
      have hvol_le : (u + δ) - ρ₀ ≤ η + δ := by linarith [hu_lt]
      calc volume Bad
          ≤ volume (Set.Icc ρ₀ (u + δ)) + volume {v | v ∈ Set.Icc (u + δ) x₁ ∧
              ∃ δ' ∈ Set.Ioc (0 : ℝ) δ₀,
                (f v : ℝ) * Real.exp (K * δ') < f (v + δ')} :=
            (measure_mono hcover).trans (measure_union_le _ _)
        _ ≤ ENNReal.ofReal (η + δ) +
              ENNReal.ofReal
                ((Real.log (f (x₁ + δ₀)) - Real.log (f (u + δ))) / K + n * η) := by
            refine add_le_add ?_ hrec
            rw [Real.volume_Icc]
            exact ENNReal.ofReal_le_ofReal hvol_le
        _ ≤ ENNReal.ofReal
              ((Real.log (f (x₁ + δ₀)) - Real.log (f x₀)) / K + (n + 1) * η) := by
            have h_pos₁ : 0 ≤ η + δ := by positivity
            have h_pos₂ : 0 ≤ (Real.log (f (x₁ + δ₀)) -
              Real.log (f (u + δ))) / K + n * η := by positivity
            rw [← ENNReal.ofReal_add h_pos₁ h_pos₂]
            apply ENNReal.ofReal_le_ofReal
            have hlog_sub : Real.log (f x₀) ≤ Real.log (f u) :=
              Real.log_le_log hfx₀ (Nat.cast_le.mpr (hmono hx₀ hu_mem hux₀))
            have hlog_step : K * δ ≤ Real.log (f (u + δ)) - Real.log (f u) :=
              le_log_sub_log_of_mul_exp_le hfu hlt.le
            exact volume_bad_right_ineq n hK hlog_sub hlog_step
        _ = ENNReal.ofReal ((Real.log (f (x₁ + δ₀)) - Real.log (f x₀)) / K +
              ↑(n + 1) * η) := by simp

private lemma volume_bad_left_le_aux {K δ₀ : ℝ} (hK : 0 < K) (hδ₀ : 0 < δ₀) (n : ℕ) :
    ∀ (f : ℝ → ℕ) (x₀ x₁ η : ℝ), 0 < η →
      MonotoneOn f (Set.Icc (x₀ - δ₀) x₁) →
      (∀ u ∈ Set.Icc (x₀ - δ₀) x₁, 1 ≤ f u) →
      f x₁ ≤ f (x₀ - δ₀) + n →
      volume {u | u ∈ Set.Icc x₀ x₁ ∧ ∃ δ ∈ Set.Ioc (0 : ℝ) δ₀,
          (f (u - δ) : ℝ) * Real.exp (K * δ) < f u} ≤
        ENNReal.ofReal ((Real.log (f x₁) - Real.log (f (x₀ - δ₀))) / K + n * η) := by
  induction n with
  | zero =>
    intro f x₀ x₁ η _hη hmono hpos _hbudget
    have : {u | u ∈ Set.Icc x₀ x₁ ∧ ∃ δ ∈ Set.Ioc (0 : ℝ) δ₀,
        (f (u - δ) : ℝ) * Real.exp (K * δ) < f u} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro u ⟨⟨hux₀, hux₁⟩, δ, ⟨hδ₁, hδ₂⟩, hlt⟩
      have hx₀ : x₀ - δ₀ ∈ Set.Icc (x₀ - δ₀) x₁ := ⟨le_rfl, by linarith⟩
      have hu : u ∈ Set.Icc (x₀ - δ₀) x₁ := ⟨by linarith, hux₁⟩
      have hu_δ_mem : u - δ ∈ Set.Icc (x₀ - δ₀) x₁ := ⟨by linarith, by linarith⟩
      have hx₁_mem : x₁ ∈ Set.Icc (x₀ - δ₀) x₁ := ⟨by linarith, le_rfl⟩
      have : f u ≤ f x₁ := hmono hu hx₁_mem hux₁
      have hle : x₀ - δ₀ ≤ u - δ := by linarith
      have : f (x₀ - δ₀) ≤ f (u - δ) := hmono hx₀ hu_δ_mem hle
      have : f (u - δ) < f u := by
        exact_mod_cast lt_of_mul_exp_lt (Nat.cast_nonneg (f (u - δ)))
          (mul_nonneg hK.le hδ₁.le) hlt
      lia
    simp_all
  | succ n ih =>
    intro f x₀ x₁ η hη hmono hpos hbudget
    set Bad := {u | u ∈ Set.Icc x₀ x₁ ∧ ∃ δ ∈ Set.Ioc (0 : ℝ) δ₀,
      (f (u - δ) : ℝ) * Real.exp (K * δ) < f u}
    rcases Set.eq_empty_or_nonempty Bad with he | hne
    · rw [he, measure_empty]
      simp
    · have : Bad ⊆ Set.Icc x₀ x₁ := fun v hv ↦ hv.1
      have hbdd : BddAbove Bad := bddAbove_Icc.mono this
      set ρ₁ := sSup Bad
      obtain ⟨u, ⟨⟨hux₀, hux₁⟩, δ, ⟨hδ₁, hδ₂⟩, hlt⟩, hu_lt⟩ :=
        (lt_csSup_iff hbdd hne).1 (sub_lt_self ρ₁ hη)
      have hu_mem : u ∈ Set.Icc (x₀ - δ₀) x₁ := ⟨by linarith, hux₁⟩
      have hu_δ_mem : u - δ ∈ Set.Icc (x₀ - δ₀) x₁ := ⟨by linarith, by linarith⟩
      have hx₁_mem : x₁ ∈ Set.Icc (x₀ - δ₀) x₁ := ⟨by linarith, le_rfl⟩
      have hfu : (0 : ℝ) < f u := Nat.cast_pos.mpr (hpos u hu_mem)
      have hfuδ : (0 : ℝ) < f (u - δ) := Nat.cast_pos.mpr (hpos _ hu_δ_mem)
      have : f (u - δ) < f u := by
        exact_mod_cast lt_of_mul_exp_lt (Nat.cast_nonneg (f (u - δ)))
          (mul_nonneg hK.le hδ₁.le) hlt
      have hcover : Bad ⊆ {v | v ∈ Set.Icc x₀ (u - δ) ∧
          ∃ δ' ∈ Set.Ioc (0 : ℝ) δ₀, (f (v - δ') : ℝ) * Real.exp (K * δ') < f v} ∪
          Set.Icc (u - δ) ρ₁ := by
        rintro v hv
        rcases le_or_gt v (u - δ) with hvu | hvu
        · exact Or.inl ⟨⟨hv.1.1, hvu⟩, hv.2⟩
        · exact Or.inr ⟨hvu.le, le_csSup hbdd hv⟩
      have hbudget_rec : f (u - δ) ≤ f (x₀ - δ₀) + n := by
        have : f u ≤ f x₁ := hmono hu_mem hx₁_mem hux₁
        lia
      have hrec := ih f x₀ (u - δ) η hη (hmono.mono (Set.Icc_subset_Icc le_rfl hu_δ_mem.2))
        (fun v hv ↦ hpos v ⟨hv.1, hv.2.trans hu_δ_mem.2⟩) hbudget_rec
      have hx₀ : x₀ - δ₀ ∈ Set.Icc (x₀ - δ₀) x₁ := ⟨le_rfl, by linarith⟩
      have hfx₀ : (0 : ℝ) < f (x₀ - δ₀) := Nat.cast_pos.mpr (hpos _ hx₀)
      have hle : x₀ - δ₀ ≤ u - δ := by linarith
      have : Real.log (f (x₀ - δ₀)) ≤ Real.log (f (u - δ)) :=
        Real.log_le_log hfx₀ (Nat.cast_le.mpr (hmono hx₀ hu_δ_mem hle))
      have hvol_le : ρ₁ - (u - δ) ≤ δ + η := by linarith [hu_lt]
      calc volume Bad
          ≤ volume {v | v ∈ Set.Icc x₀ (u - δ) ∧
              ∃ δ' ∈ Set.Ioc (0 : ℝ) δ₀,
                (f (v - δ') : ℝ) * Real.exp (K * δ') < f v} +
              volume (Set.Icc (u - δ) ρ₁) :=
            (measure_mono hcover).trans (measure_union_le _ _)
        _ ≤ ENNReal.ofReal ((Real.log (f (u - δ)) - Real.log (f (x₀ - δ₀))) / K + n * η) +
              ENNReal.ofReal (δ + η) := by
            refine add_le_add hrec ?_
            rw [Real.volume_Icc]
            exact ENNReal.ofReal_le_ofReal hvol_le
        _ ≤ ENNReal.ofReal
              ((Real.log (f x₁) - Real.log (f (x₀ - δ₀))) / K + (n + 1) * η) := by
            have h_pos₁ : 0 ≤ (Real.log (f (u - δ)) -
              Real.log (f (x₀ - δ₀))) / K + n * η := by positivity
            have h_pos₂ : 0 ≤ δ + η := by positivity
            rw [← ENNReal.ofReal_add h_pos₁ h_pos₂]
            apply ENNReal.ofReal_le_ofReal
            have hlog_sub : Real.log (f u) ≤ Real.log (f x₁) :=
              Real.log_le_log hfu (Nat.cast_le.mpr (hmono hu_mem hx₁_mem hux₁))
            have hlog_step : K * δ ≤ Real.log (f u) - Real.log (f (u - δ)) :=
              le_log_sub_log_of_mul_exp_le hfuδ hlt.le
            exact volume_bad_left_ineq n hK hlog_sub hlog_step
        _ = ENNReal.ofReal ((Real.log (f x₁) - Real.log (f (x₀ - δ₀))) / K +
              ↑(n + 1) * η) := by simp

private lemma volume_bad_right_le {K δ₀ : ℝ} (hK : 0 < K) (hδ₀ : 0 < δ₀)
    (f : ℝ → ℕ) (x₀ x₁ : ℝ) (hmono : MonotoneOn f (Set.Icc x₀ (x₁ + δ₀)))
    (hpos : ∀ u ∈ Set.Icc x₀ (x₁ + δ₀), 1 ≤ f u) :
    volume {u | u ∈ Set.Icc x₀ x₁ ∧ ∃ δ ∈ Set.Ioc (0 : ℝ) δ₀,
        (f u : ℝ) * Real.exp (K * δ) < f (u + δ)} ≤
      ENNReal.ofReal ((Real.log (f (x₁ + δ₀)) - Real.log (f x₀)) / K) := by
  set n := f (x₁ + δ₀) - f x₀
  refine ENNReal.le_of_forall_pos_le_add fun ε' hε' _ ↦ ?_
  have hη : (0 : ℝ) < (ε' : ℝ) / (n + 1) := by positivity
  have : n * ((ε' : ℝ) / (n + 1)) ≤ ε' := nat_mul_div_self_add_one_le n ε' ε'.coe_nonneg
  have hbudget : f (x₁ + δ₀) ≤ f x₀ + n := by lia
  exact (volume_bad_right_le_aux hK hδ₀ n f x₀ x₁ _ hη hmono hpos hbudget).trans
    (ENNReal.ofReal_add_le.trans (add_le_add le_rfl (ENNReal.ofReal_le_coe.2 this)))

private lemma volume_bad_left_le {K δ₀ : ℝ} (hK : 0 < K) (hδ₀ : 0 < δ₀) (f : ℝ → ℕ)
    (x₀ x₁ : ℝ) (hmono : MonotoneOn f (Set.Icc (x₀ - δ₀) x₁))
    (hpos : ∀ u ∈ Set.Icc (x₀ - δ₀) x₁, 1 ≤ f u) :
    volume {u | u ∈ Set.Icc x₀ x₁ ∧ ∃ δ ∈ Set.Ioc (0 : ℝ) δ₀,
        (f (u - δ) : ℝ) * Real.exp (K * δ) < f u} ≤
      ENNReal.ofReal ((Real.log (f x₁) - Real.log (f (x₀ - δ₀))) / K) := by
  set n := f x₁ - f (x₀ - δ₀)
  refine ENNReal.le_of_forall_pos_le_add fun ε' hε' _ ↦ ?_
  have hη : (0 : ℝ) < (ε' : ℝ) / (n + 1) := by positivity
  have : n * ((ε' : ℝ) / (n + 1)) ≤ ε' := nat_mul_div_self_add_one_le n ε' ε'.coe_nonneg
  have hbudget : f x₁ ≤ f (x₀ - δ₀) + n := by lia
  exact (volume_bad_left_le_aux hK hδ₀ n f x₀ x₁ _ hη hmono hpos hbudget).trans
    (ENNReal.ofReal_add_le.trans (add_le_add le_rfl (ENNReal.ofReal_le_coe.2 this)))

lemma exists_good_scale {K δ₀ a : ℝ} (hK : 0 < K) (hδ₀ : 0 < δ₀) (f : ℝ → ℕ)
    (hmono : MonotoneOn f (Set.Icc (-δ₀) (a + δ₀)))
    (hpos : ∀ u ∈ Set.Icc (-δ₀) (a + δ₀), 1 ≤ f u)
    (hbudget_right : (Real.log (f (a + δ₀)) - Real.log (f 0)) / K ≤ Real.log 8 / 30)
    (hbudget_left : (Real.log (f a) - Real.log (f (0 - δ₀))) / K ≤ Real.log 8 / 30)
    (ha_lt : Real.log 8 / 15 < a) :
    ∃ u ∈ Set.Icc (0 : ℝ) a,
      (∀ δ ∈ Set.Ioc (0 : ℝ) δ₀, (f (u + δ) : ℝ) ≤ f u * Real.exp (K * δ)) ∧
      (∀ δ ∈ Set.Ioc (0 : ℝ) δ₀, (f u : ℝ) ≤ f (u - δ) * Real.exp (K * δ)) := by
  by_contra hcon
  have hsub : Set.Icc (0 : ℝ) a ⊆
      {u | u ∈ Set.Icc (0 : ℝ) a ∧ ∃ δ ∈ Set.Ioc (0 : ℝ) δ₀,
        (f u : ℝ) * Real.exp (K * δ) < f (u + δ)} ∪
      {u | u ∈ Set.Icc (0 : ℝ) a ∧ ∃ δ ∈ Set.Ioc (0 : ℝ) δ₀,
        (f (u - δ) : ℝ) * Real.exp (K * δ) < f u} := by
    intro u hu
    have h : ¬((∀ δ ∈ Set.Ioc (0 : ℝ) δ₀,
        (f (u + δ) : ℝ) ≤ f u * Real.exp (K * δ)) ∧
        (∀ δ ∈ Set.Ioc (0 : ℝ) δ₀, (f u : ℝ) ≤ f (u - δ) * Real.exp (K * δ))) :=
      fun hrl ↦ hcon ⟨u, hu, hrl⟩
    rw [not_and_or] at h
    obtain h | h := h
    · push Not at h
      exact Or.inl ⟨hu, h⟩
    · push Not at h
      exact Or.inr ⟨hu, h⟩
  have hsub_right : Set.Icc 0 (a + δ₀) ⊆ Set.Icc (-δ₀) (a + δ₀) :=
    fun _ hx ↦ ⟨by linarith [hx.1, hδ₀], hx.2⟩
  have hvol_right := volume_bad_right_le hK hδ₀ f 0 a
    (hmono.mono hsub_right)
    (fun u hu ↦ hpos u ⟨by linarith [hu.1, hδ₀], hu.2⟩)
  have hsub_left : Set.Icc (0 - δ₀) a ⊆ Set.Icc (-δ₀) (a + δ₀) :=
    fun _ hx ↦ ⟨by linarith [hx.1], by linarith [hx.2, hδ₀]⟩
  have hvol_left := volume_bad_left_le hK hδ₀ f 0 a
    (hmono.mono hsub_left)
    (fun u hu ↦ hpos u ⟨by linarith [hu.1], by linarith [hu.2, hδ₀]⟩)
  have hvol : volume (Set.Icc (0 : ℝ) a) ≤
      ENNReal.ofReal (Real.log 8 / 30) + ENNReal.ofReal (Real.log 8 / 30) := by
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    exact add_le_add (hvol_right.trans (ENNReal.ofReal_le_ofReal hbudget_right))
      (hvol_left.trans (ENNReal.ofReal_le_ofReal hbudget_left))
  have : (0 : ℝ) ≤ Real.log 8 / 30 := by positivity
  rw [Real.volume_Icc, ← ENNReal.ofReal_add this this] at hvol
  have : 0 ≤ Real.log 8 / 30 + Real.log 8 / 30 := by positivity
  rw [ENNReal.ofReal_le_ofReal_iff this] at hvol
  linarith

end ScaleSelection

lemma mul_exp_le_one_of_le {x y : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (hy : y ≤ (61 / 100) * x) :
    (1 - x) * Real.exp y ≤ 1 := by
  set z := (61 / 100) * x
  have hexp₁ : 1 - z ≤ Real.exp (-z) := by
    have := Real.add_one_le_exp (-z)
    linarith
  have h_one_sub_bound : (1 - z) * Real.exp z ≤ 1 := by
    have h_eq : Real.exp (-z) * Real.exp z = 1 := by
      rw [← Real.exp_add]
      simp
    exact (mul_le_mul_of_nonneg_right hexp₁ (Real.exp_pos _).le).trans_eq h_eq
  have h_nonneg₂ : 0 ≤ 1 - x := by linarith
  have h_trans₁ : (1 - x) * Real.exp y ≤ (1 - x) * Real.exp z :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hy) h_nonneg₂
  have h_trans₂ : (1 - x) * Real.exp z ≤ (1 - z) * Real.exp z := by
    have : 1 - x ≤ 1 - z := by
      dsimp [z]
      linarith
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  exact h_trans₁.trans (h_trans₂.trans h_one_sub_bound)

lemma exp_le_one_add_of_le {x y : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (hy : y ≤ x * (3 / 5)) :
    Real.exp y ≤ 1 + x := by
  have h_one_sub_x : 0 ≤ 1 - x := by linarith
  have hcv : Real.exp ((1 - x) * 0 + x * (3 / 5)) ≤
      (1 - x) * Real.exp 0 + x * Real.exp (3 / 5) := by
    refine convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) h_one_sub_x hx₀ ?_
    norm_num
  simp only [mul_zero, zero_add, Real.exp_zero, mul_one] at hcv
  have h_log_two : (3 : ℝ) / 5 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have he : Real.exp ((3 : ℝ) / 5) ≤ 2 :=
    (Real.exp_le_exp.2 h_log_two).trans_eq (Real.exp_log zero_lt_two)
  have h_trans : 1 - x + x * Real.exp (3 / 5) ≤ 1 + x := by
    nlinarith [mul_le_mul_of_nonneg_left he hx₀]
  exact (Real.exp_le_exp.2 hy).trans (hcv.trans h_trans)

lemma one_sub_mul_exp_le_one_of_scale {d κ δ K : ℝ} (hd : 1 ≤ d) (hK : K = 60 * d)
    (hκ : 100 * d * κ < 1) (hδ : δ ≤ (100 / 99) * κ) (hκ₀ : 0 ≤ d * κ) :
    (1 - 100 * d * κ) * Real.exp (K * δ) ≤ 1 := by
  have hKδ : K * δ ≤ (61 / 100) * (100 * d * κ) := by
    rw [hK]
    have : 60 * d * δ ≤ 60 * d * ((100 / 99) * κ) := by nlinarith
    linarith
  have h_nonneg : 0 ≤ 100 * d * κ := by linarith [hκ₀]
  exact mul_exp_le_one_of_le h_nonneg hκ.le hKδ

lemma exp_le_one_add_of_scale {d κ δ K : ℝ} (hd : 1 ≤ d) (hK : K = 60 * d)
    (hκ : 100 * d * κ ≤ 1) (hδ : δ ≤ κ) (hκ₀ : 0 ≤ d * κ) :
    Real.exp (K * δ) ≤ 1 + 100 * d * κ := by
  have hKδ : K * δ ≤ 100 * d * κ * (3 / 5) := by
    rw [hK]
    have : 60 * d * δ ≤ 60 * d * κ := by nlinarith
    linarith
  have h_nonneg : 0 ≤ 100 * d * κ := by linarith [hκ₀]
  exact exp_le_one_add_of_le h_nonneg hκ hKδ

lemma le_log_four_thirds : (1 / 4 : ℝ) ≤ Real.log (4 / 3) := by
  have h_pos : (0 : ℝ) < 4 / 3 := by norm_num
  have : 1 - (4 / 3)⁻¹ ≤ Real.log (4 / 3) := Real.one_sub_inv_le_log_of_pos h_pos
  linarith

lemma log_three_halves_add_two_mul_inv_hundred_mul_le_log_two {d : ℝ} (hd : 1 ≤ d) :
    Real.log (3 / 2) + 2 * (100 * d : ℝ)⁻¹ ≤ Real.log 2 := by
  have h1 : (3 / 2 : ℝ) ≠ 0 := by norm_num
  have h2 : (4 / 3 : ℝ) ≠ 0 := by norm_num
  have : Real.log 2 = Real.log (3 / 2) + Real.log (4 / 3) := by
    rw [← Real.log_mul h1 h2]
    norm_num
  have : (100 * d : ℝ)⁻¹ ≤ 1 / 100 := by
    rw [one_div]
    have h_pos : (0 : ℝ) < 100 := by norm_num
    have h_le : (100 : ℝ) ≤ 100 * d := by linarith
    exact inv_anti₀ h_pos h_le
  have : 2 * (100 * d : ℝ)⁻¹ ≤ 1 / 50 := by linarith
  linarith [le_log_four_thirds]

lemma five_mul_exp_log_three_halves_add_le_eight {d : ℝ} (hd : 1 ≤ d) :
    5 * Real.exp (Real.log (3 / 2) + 2 * (100 * d : ℝ)⁻¹) ≤ 8 := by
  have : Real.log (3 / 2) + 2 * (100 * d : ℝ)⁻¹ ≤ Real.log (8 / 5) := by
    have h1 : (3 / 2 : ℝ) ≠ 0 := by norm_num
    have h2 : (16 / 15 : ℝ) ≠ 0 := by norm_num
    have : Real.log (8 / 5) = Real.log (3 / 2) + Real.log (16 / 15) := by
      rw [← Real.log_mul h1 h2]
      norm_num
    have h_pos : (0 : ℝ) < 16 / 15 := by norm_num
    have : (1 / 16 : ℝ) ≤ Real.log (16 / 15) := by
      linarith [Real.one_sub_inv_le_log_of_pos h_pos]
    have : (100 * d : ℝ)⁻¹ ≤ 1 / 100 := by
      rw [one_div]
      have h_pos : (0 : ℝ) < 100 := by norm_num
      have h_le : (100 : ℝ) ≤ 100 * d := by linarith
      exact inv_anti₀ h_pos h_le
    have : 2 * (100 * d : ℝ)⁻¹ ≤ 1 / 50 := by linarith
    linarith
  have : Real.exp (Real.log (3 / 2) + 2 * (100 * d : ℝ)⁻¹) ≤ 8 / 5 := by
    refine (Real.exp_le_exp.2 this).trans_eq ?_
    have h_pos : (0 : ℝ) < 8 / 5 := by norm_num
    exact Real.exp_log h_pos
  linarith

lemma log_eight_div_fifteen_lt_log_three_halves : Real.log 8 / 15 < Real.log (3 / 2) := by
  have h_pos : (0 : ℝ) < 15 := by norm_num
  rw [div_lt_iff₀ h_pos]
  have : Real.log ((3 / 2) ^ 15) = Real.log (3 / 2) * 15 := by
    rw [Real.log_pow]
    ring
  have h1 : (0 : ℝ) < 8 := by norm_num
  have h2 : (8 : ℝ) < (3 / 2) ^ 15 := by norm_num
  exact (Real.log_lt_log h1 h2).trans_eq this

/-- **Bohr Set Regularity**. Any Bohr set can be dilated by a small amount to become a regular Bohr
set. -/
lemma regularity (B : BohrSet G) (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    ∃ ρ : ℝ, ε ≤ ρ ∧ ρ ≤ 2 * ε ∧ (ρ • B).IsRegular := by
  have hε : 0 < ε := hε₀
  have _ : ε < 1 := hε₁
  classical
  obtain hd_zero | hd_pos := Nat.eq_zero_or_pos B.dimSqRank
  · refine ⟨ε, le_rfl, ?_, ?_, ?_⟩
    · linarith
    · intro κ _hκ₀ hκ
      have : κ = 0 := by
        rw [dimSqRank_smul, hd_zero] at hκ
        linarith
      subst this
      norm_num [one_smul]
    · intro κ _hκ₀ hκ
      have : κ = 0 := by
        rw [dimSqRank_smul, hd_zero] at hκ
        linarith
      subst this
      norm_num [one_smul]
  · obtain hinf | hfin := ((((2 * ε) • B : BohrSet G) : Set G)).infinite_or_finite
    · have h₂ε : (0 : ℝ) < 2 * ε := by linarith
      refine ⟨2 * ε, ?_, le_rfl, ?_, ?_⟩
      · linarith
      · intro κ _hκ₀ _hκ
        have : Infinite ↥((2 * ε) • B) := hinf.to_subtype
        simp [Nat.card_eq_zero_of_infinite]
      · intro κ hκ₀ _hκ
        have hsub : ((((2 * ε) • B : BohrSet G)) : Set G) ⊆
              (((1 + κ) • ((2 * ε) • B) : BohrSet G) : Set G) := by
          rw [smul_smul]
          refine chordSet_smul_subset_smul_of_nonneg_right h₂ε.le ?_
          nlinarith
        have : Infinite ↥((1 + κ) • (2 * ε) • B) := (hinf.mono hsub).to_subtype
        have : Infinite ↥((2 * ε) • B) := hinf.to_subtype
        simp [Nat.card_eq_zero_of_infinite]
    · set d := B.dimSqRank with hd_def
      have hd₁ : (1 : ℝ) ≤ d := by norm_cast
      set κ₀ : ℝ := (100 * d : ℝ)⁻¹ with hκ₀_def
      have hκ₀_le : κ₀ ≤ 1 / 100 := by
        rw [hκ₀_def, one_div]
        refine inv_anti₀ ?_ ?_
        · norm_num
        · linarith [hd₁]
      set δ₀ : ℝ := 2 * κ₀
      have hδ₀ : 0 < δ₀ := by positivity
      set K : ℝ := 60 * d with hK_def
      have hK : 0 < K := by positivity
      set a : ℝ := Real.log (3 / 2) with ha_def
      have h_pos : (1 : ℝ) < 3 / 2 := by norm_num
      have ha : 0 < a := by
        rw [ha_def]
        exact Real.log_pos h_pos
      have hcap : a + δ₀ ≤ Real.log 2 :=
        log_three_halves_add_two_mul_inv_hundred_mul_le_log_two hd₁
      set f : ℝ → ℕ := fun u ↦ Nat.card ↥((ε * Real.exp u) • B)
      have hscale_pos : ∀ u : ℝ, 0 < ε * Real.exp u := fun u ↦ mul_pos hε (Real.exp_pos u)
      have hscale_le (u : ℝ) (hu : u ≤ a + δ₀) : ε * Real.exp u ≤ 2 * ε := by
        have hexp_le : Real.exp u ≤ 2 := by
          calc Real.exp u ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 (hu.trans hcap)
            _ = 2 := Real.exp_log zero_lt_two
        nlinarith [mul_le_mul_of_nonneg_left hexp_le hε.le]
      have hsubset (u v : ℝ) (huv : u ≤ v) : (((ε * Real.exp u) • B : BohrSet G) : Set G) ⊆
          (((ε * Real.exp v) • B : BohrSet G) : Set G) :=
        chordSet_smul_subset_smul_of_nonneg_right (hscale_pos u).le
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 huv) hε.le)
      have hfin_u (u : ℝ) (hu : u ≤ a + δ₀) :
          (((ε * Real.exp u) • B : BohrSet G) : Set G).Finite :=
        hfin.subset <| chordSet_smul_subset_smul_of_nonneg_right (hscale_pos u).le (hscale_le u hu)
      have hmono : MonotoneOn f (Set.Icc (-δ₀) (a + δ₀)) := by
        intro u hu v hv huv
        exact Nat.card_mono (hfin_u v hv.2) (hsubset u v huv)
      have hpos (u : ℝ) (hu : u ∈ Set.Icc (-δ₀) (a + δ₀)) : 1 ≤ f u := by
        haveI : Finite ↥(((ε * Real.exp u) • B : BohrSet G) : Set G) :=
          (hfin_u u hu.2).to_subtype
        haveI : Nonempty ↥(((ε * Real.exp u) • B : BohrSet G) : Set G) :=
          Set.Nonempty.to_subtype ⟨1, one_mem_chordSet⟩
        exact Nat.card_pos
      have hbase : 5 * Real.exp (a + δ₀) ≤ 8 :=
        five_mul_exp_log_three_halves_add_le_eight hd₁
      have hlog_f (v u : ℝ) (huv : u ≤ v) (hgap : v - u ≤ a + δ₀)
          (hu : u ∈ Set.Icc (-δ₀) (a + δ₀)) (hv : v ∈ Set.Icc (-δ₀) (a + δ₀)) :
          (Real.log (f v) - Real.log (f u)) / K ≤ Real.log 8 / 30 :=
        log_natCard_scale_sub_le huv hgap hbase (hpos u hu) (hpos v hv)
          (by rw [hK_def, hd_def]) hK
      have : Set.Icc 0 (a + δ₀) ⊆ Set.Icc (-δ₀) (a + δ₀) :=
        fun _ hx ↦ ⟨by linarith [hx.1, hδ₀], hx.2⟩
      have hvol_right := volume_bad_right_le hK hδ₀ f 0 a
        (hmono.mono this)
        (fun u hu ↦ hpos u ⟨by linarith [hu.1, hδ₀], hu.2⟩)
      have : Set.Icc (0 - δ₀) a ⊆ Set.Icc (-δ₀) (a + δ₀) :=
        fun _ hx ↦ ⟨by linarith [hx.1], by linarith [hx.2, hδ₀]⟩
      have hvol_left := volume_bad_left_le hK hδ₀ f 0 a
        (hmono.mono this)
        (fun u hu ↦ hpos u ⟨by linarith [hu.1], by linarith [hu.2, hδ₀]⟩)
      have hbudget_right : (Real.log (f (a + δ₀)) - Real.log (f 0)) / K ≤ Real.log 8 / 30 := by
        refine hlog_f (a + δ₀) 0 ?_ ?_ ⟨?_, ?_⟩ ⟨?_, ?_⟩
        all_goals linarith [ha]
      have hbudget_left : (Real.log (f a) - Real.log (f (0 - δ₀))) / K ≤ Real.log 8 / 30 := by
        refine hlog_f a (0 - δ₀) ?_ ?_ ⟨?_, ?_⟩ ⟨?_, ?_⟩
        all_goals linarith [ha]
      have hlt : Real.log 8 / 15 < a := log_eight_div_fifteen_lt_log_three_halves
      obtain ⟨u, huI, hgood_right, hgood_left⟩ :=
        exists_good_scale hK hδ₀ f hmono hpos hbudget_right hbudget_left hlt
      have : 1 ≤ Real.exp u := Real.one_le_exp huI.1
      have hexp_u₂ : Real.exp u ≤ 3 / 2 := by
        have h_pos : (0 : ℝ) < 3 / 2 := by norm_num
        have : Real.exp a = 3 / 2 := by rw [ha_def, Real.exp_log h_pos]
        exact (Real.exp_le_exp.2 huI.2).trans_eq this
      clear hvol_right hvol_left hbudget_right hbudget_left hlog_f
      clear hmono hpos hsubset hfin_u hscale_le hscale_pos hbase hcap ha hfin huI
      refine ⟨ε * Real.exp u, ?_, ?_, ?_, ?_⟩
      · nlinarith [this, hε.le]
      · nlinarith [hexp_u₂, hε.le]
      · intro κ hκ₀ hκ
        rw [dimSqRank_smul, ← hd_def] at hκ ⊢
        rcases le_or_gt 1 (100 * (d : ℝ) * κ) with hbig | hsmall
        · have : 1 - 100 * (d : ℝ) * κ ≤ 0 := by linarith
          have : (0 : ℝ) ≤ Nat.card ↥((1 - κ) • ((ε * Real.exp u) • B)) :=
            Nat.cast_nonneg _
          nlinarith
        obtain rfl | hκ_pos := eq_or_lt_of_le hκ₀
        · simp [one_smul]
        have hκκ₀ : κ ≤ κ₀ := hκ
        have hκ_le : κ ≤ 1 / 100 := hκκ₀.trans hκ₀_le
        have h_one_sub_κ : (0 : ℝ) < 1 - κ := by linarith
        set δ : ℝ := -Real.log (1 - κ)
        have hδ : 0 < δ := neg_pos.2 (Real.log_neg h_one_sub_κ (sub_lt_self 1 hκ_pos))
        have hδ_le_κ : δ ≤ (100 / 99) * κ := neg_log_one_sub_le_div hκ_pos hκ_le
        have hδ_le : δ ≤ δ₀ := by linarith
        have hleft := hgood_left δ ⟨hδ, hδ_le⟩
        have hu_sub_δ : u - δ = u + Real.log (1 - κ) := by linarith
        have : ((1 - κ) • ((ε * Real.exp u) • B)) = (ε * Real.exp (u - δ)) • B := by
          rw [smul_smul, hu_sub_δ, Real.exp_add, Real.exp_log h_one_sub_κ]
          congr 1
          ring
        rw [this]
        have hK_eq : K = 60 * d := by rw [hK_def, hd_def]
        have hnonneg : 0 ≤ d * κ := by positivity
        have : (1 - 100 * (d : ℝ) * κ) * Real.exp (K * δ) ≤ 1 :=
          one_sub_mul_exp_le_one_of_scale hd₁ hK_eq hsmall hδ_le_κ hnonneg
        have : (0 : ℝ) ≤ 1 - 100 * (d : ℝ) * κ := by linarith
        have : (0 : ℝ) ≤ f (u - δ) := Nat.cast_nonneg _
        nlinarith [hleft]
      · intro κ hκ₀ hκ
        rw [dimSqRank_smul, ← hd_def] at hκ ⊢
        obtain rfl | hκ_pos := eq_or_lt_of_le hκ₀
        · simp [one_smul]
        have hκκ₀ : κ ≤ κ₀ := hκ
        have hle_one : 100 * (d : ℝ) * κ ≤ 1 := by
          have h_pos : (0 : ℝ) < 100 * d := by positivity
          rw [hκ₀_def, ← one_div, le_div_iff₀ h_pos] at hκκ₀
          linarith
        set δ : ℝ := Real.log (1 + κ) with hδ_def
        have h_pos₁ : (1 : ℝ) < 1 + κ := by linarith
        have hδ : 0 < δ := Real.log_pos h_pos₁
        have h_pos₂ : (0 : ℝ) < 1 + κ := by linarith
        have hδ_le_κ : δ ≤ κ := by
          rw [hδ_def]
          linarith [Real.log_le_sub_one_of_pos h_pos₂]
        have hδ_le : δ ≤ δ₀ := by linarith
        have hright := hgood_right δ ⟨hδ, hδ_le⟩
        have : ((1 + κ) • ((ε * Real.exp u) • B)) = (ε * Real.exp (u + δ)) • B := by
          have h_pos : 0 < 1 + κ := by linarith
          rw [smul_smul, Real.exp_add, Real.exp_log h_pos]
          congr 1
          ring
        rw [this]
        have hK_eq : K = 60 * d := by rw [hK_def, hd_def]
        have hnonneg : 0 ≤ d * κ := by positivity
        have : Real.exp (K * δ) ≤ 1 + 100 * (d : ℝ) * κ :=
          exp_le_one_add_of_scale hd₁ hK_eq hle_one hδ_le_κ hnonneg
        change (f (u + δ) : ℝ) ≤ (1 + 100 * (d : ℝ) * κ) * f u
        have : (0 : ℝ) ≤ f u := Nat.cast_nonneg _
        have h_trans : f u * Real.exp (K * δ) ≤ (1 + 100 * (d : ℝ) * κ) * f u := by nlinarith
        exact hright.trans h_trans

end BohrSet
