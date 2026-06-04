/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import MeanFourier.UnitaryDual

import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Bohr sets
-/

public section

open scoped ENNReal NNReal Finset

variable {G : Type*}

variable (G) in
/-- A *Bohr set* `B` on a group `G` is a finite set of unitary representations of `G`, called the
*frequencies*, along with an extended non-negative real number for each frequency `ψ`, called the
*width of `B` at `ψ`*.

A Bohr set `B` is thought of as the set `{x | ∀ ψ ∈ B.frequencies, ‖1 - ψ x‖ ≤ B.width ψ}`. This is
the *chord-length* convention. The arc-length convention would instead be
`{x | ∀ ψ ∈ B.frequencies, |arg (ψ x)| ≤ B.width ψ}`.

Note that this set **does not** uniquely determine `B` (in particular, it does not uniquely
determine either `B.frequencies` or `B.width`). -/
@[ext]
structure BohrSet [Group G] where
  frequencies : Finset (UnitaryDual ℂ G)
  /-- The width of a Bohr set at a frequency. Note that this width corresponds to chord-length. -/
  ewidth : UnitaryDual ℂ G → ℝ≥0∞
  mem_frequencies : ∀ ψ, ψ ∈ frequencies ↔ ewidth ψ < ⊤

namespace BohrSet
section Group
variable [Group G] {B : BohrSet G} {ψ : UnitaryDual ℂ G} {x y : G}

def width (B : BohrSet G) (ψ : UnitaryDual ℂ G) : ℝ≥0 := (B.ewidth ψ).toNNReal

lemma coe_width (hψ : ψ ∈ B.frequencies) : B.width ψ = B.ewidth ψ := by
  refine ENNReal.coe_toNNReal ?_
  rwa [←lt_top_iff_ne_top, ←B.mem_frequencies]

lemma ewidth_eq_top_iff : ψ ∉ B.frequencies ↔ B.ewidth ψ = ⊤ := by
  simp [B.mem_frequencies]

alias ⟨ewidth_eq_top_of_not_mem_frequencies, _⟩ := ewidth_eq_top_iff

lemma width_eq_zero_of_not_mem_frequencies (hψ : ψ ∉ B.frequencies) : B.width ψ = 0 := by
  rw [width, ewidth_eq_top_of_not_mem_frequencies hψ, ENNReal.toNNReal_top]

lemma ewidth_injective : Function.Injective (BohrSet.ewidth (G := G)) := by
  intro B₁ B₂ h
  ext ψ
  case ewidth => rw [h]
  case frequencies => rw [B₁.mem_frequencies, B₂.mem_frequencies, h]

/-- Construct a Bohr set on a finite group given an extended width function. -/
noncomputable def ofEwidth [Finite G] (ewidth : UnitaryDual ℂ G → ℝ≥0∞) : BohrSet G where
  frequencies := {ψ | ewidth ψ < ⊤}
  ewidth := ewidth
  mem_frequencies ψ := by simp

/-- Construct a Bohr set on a finite group given a width function and a frequency set. -/
noncomputable def ofWidth (width : UnitaryDual ℂ G → ℝ≥0) (freq : Finset (UnitaryDual ℂ G)) :
    BohrSet G where
  frequencies := freq
  ewidth ψ := open scoped Classical in if ψ ∈ freq then width ψ else ⊤
  mem_frequencies ψ := by simp [lt_top_iff_ne_top]

@[ext]
lemma ext_width {B B' : BohrSet G} (freq : B.frequencies = B'.frequencies)
    (width : ∀ ψ : UnitaryDual ℂ G, ψ ∈ B.frequencies → B.width ψ = B'.width ψ) :
    B = B' := by
  ext
  case frequencies => rw [freq]
  case ewidth ψ =>
    by_cases hψ : ψ ∈ B.frequencies
    case pos =>
      rw [←coe_width hψ, width _ hψ, coe_width]
      rwa [←freq]
    case neg =>
      rw [ewidth_eq_top_of_not_mem_frequencies hψ, ewidth_eq_top_of_not_mem_frequencies]
      rwa [←freq]

/-! ### Coercion, membership -/

/-- The set corresponding to a Bohr set `B` is `{x | ∀ ψ ∈ B.frequencies, ‖1 - ψ x‖ ≤ B.width ψ}`.
This is the *chord-length* convention. The arc-length convention would instead be
`{x | ∀ ψ ∈ B.frequencies, |arg (ψ x)| ≤ B.width ψ}`.

Note that this set **does not** uniquely determine `B`. -/
@[coe] def chordSet (B : BohrSet G) : Set G :=
  {x | ∀ ψ, ‖1 - (ψ x : ψ.E →L[ℂ] ψ.E)‖₊ ≤ B.ewidth ψ}

/-- Given the Bohr set `B`, `B.Elem` is the `Type` of elements of `B`. -/
@[coe] abbrev Elem (B : BohrSet G) : Type _ := B.chordSet

instance instCoe : Coe (BohrSet G) (Set G) := ⟨chordSet⟩
instance instCoeSort : CoeSort (BohrSet G) (Type _) := ⟨Elem⟩

lemma mem_chordSet_iff_nnnorm_ewidth :
    x ∈ B.chordSet ↔ ∀ ψ, ‖1 - (ψ x : ψ.E →L[ℂ] ψ.E)‖₊ ≤ B.ewidth ψ := .rfl

lemma mem_chordSet_iff_nnnorm_width :
    x ∈ B.chordSet ↔ ∀ ⦃ψ⦄, ψ ∈ B.frequencies → ‖1 - (ψ x : ψ.E →L[ℂ] ψ.E)‖₊ ≤ B.width ψ := by
  refine forall_congr' fun ψ => ?_
  constructor
  case mpr =>
    intro h
    rcases eq_top_or_lt_top (B.ewidth ψ) with h₁ | h₁
    case inl => simp [h₁]
    case inr =>
      have : ψ ∈ B.frequencies := by simp [mem_frequencies, h₁]
      specialize h this
      rwa [← ENNReal.coe_le_coe, coe_width this] at h
  case mp =>
    intro h₁ h₂
    rwa [← ENNReal.coe_le_coe, coe_width h₂]

lemma mem_chordSet_iff_norm_width :
    x ∈ B.chordSet ↔ ∀ ⦃ψ⦄, ψ ∈ B.frequencies → ‖1 - (ψ x : ψ.E →L[ℂ] ψ.E)‖ ≤ B.width ψ :=
  mem_chordSet_iff_nnnorm_width

@[simp, norm_cast] lemma coeSort_coe (B : BohrSet G) : ↥(B : Set G) = B := rfl

@[simp] lemma one_mem_chordSet : 1 ∈ B.chordSet := by simp [mem_chordSet_iff_nnnorm_width]

@[simp] lemma inv_mem_chordSet : x⁻¹ ∈ B.chordSet ↔ x ∈ B.chordSet := by
  refine forall_congr' fun ψ ↦ ?_
  rw [← nnnorm_map ContinuousLinearMap.adjoint]
  simp [-LinearIsometryEquiv.toContinuousLinearEquiv_symm, LinearIsometryEquiv.inv_def]

@[simp] lemma inv_chordSet : B.chordSet⁻¹ = B.chordSet := by ext; simp

@[simp] lemma conj_mem_chordSet : y * x * y⁻¹ ∈ B.chordSet ↔ x ∈ B.chordSet := by
  simp only [mem_chordSet_iff_nnnorm_ewidth]
  congr! 3 with ψ
  calc
    ‖1 - (ψ.ρ (y * x * y⁻¹) : ψ.E →L[ℂ] ψ.E)‖₊
    _ = ‖ψ.ρ y * (1 - ψ.ρ x : ψ.E →L[ℂ] ψ.E) * ψ.ρ y⁻¹‖₊ := by
      simp [mul_sub, sub_mul, ← ContinuousLinearEquiv.toContinuousLinearMap_mul]
    _ = ‖1 - (ψ.ρ x : ψ.E →L[ℂ] ψ.E)‖₊ := by simp [-map_inv]

/-! ### Lattice structure -/

noncomputable instance : Max (BohrSet G) where
  max B₁ B₂ := {
    frequencies := B₁.frequencies ∩ B₂.frequencies,
    ewidth ψ := B₁.ewidth ψ ⊔ B₂.ewidth ψ,
    mem_frequencies ψ := by simp [mem_frequencies]
  }

noncomputable instance : Min (BohrSet G) where
  min B₁ B₂ := {
    frequencies := B₁.frequencies ∪ B₂.frequencies,
    ewidth ψ := B₁.ewidth ψ ⊓ B₂.ewidth ψ,
    mem_frequencies ψ := by simp [mem_frequencies]
  }

noncomputable instance [Finite G] : Bot (BohrSet G) where
  bot.frequencies := .univ
  bot.ewidth := 0
  bot.mem_frequencies := by simp

noncomputable instance : Top (BohrSet G) where
  top.frequencies := ∅
  top.ewidth := ⊤
  top.mem_frequencies := by simp

instance : Preorder (BohrSet G) := .lift ewidth

noncomputable instance : DistribLattice (BohrSet G) :=
  ewidth_injective.distribLattice BohrSet.ewidth .rfl .rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

lemma le_iff_ewidth {B₁ B₂ : BohrSet G} : B₁ ≤ B₂ ↔ ∀ ⦃ψ⦄, B₁.ewidth ψ ≤ B₂.ewidth ψ := .rfl

@[gcongr]
lemma frequencies_anti {B₁ B₂ : BohrSet G} (h : B₁ ≤ B₂) : B₂.frequencies ⊆ B₁.frequencies := by
  intro ψ hψ
  simp only [mem_frequencies] at hψ ⊢
  exact (h ψ).trans_lt hψ

lemma frequencies_antitone : Antitone (frequencies : BohrSet G → _) := fun _ _ ↦ frequencies_anti

lemma le_iff_width {B₁ B₂ : BohrSet G} :
    B₁ ≤ B₂ ↔
      B₂.frequencies ⊆ B₁.frequencies ∧ ∀ ⦃ψ⦄, ψ ∈ B₂.frequencies → B₁.width ψ ≤ B₂.width ψ where
  mp h := by
    refine ⟨frequencies_anti h, fun ψ hψ => ?_⟩
    rw [← ENNReal.coe_le_coe, coe_width hψ, coe_width (frequencies_anti h hψ)]
    exact h ψ
  mpr := by
    rintro ⟨h₁, h₂⟩ ψ
    by_cases ψ ∈ B₂.frequencies
    case neg h' => simp [ewidth_eq_top_of_not_mem_frequencies h']
    case pos h' =>
      rw [←coe_width h', ←coe_width (h₁ h'), ENNReal.coe_le_coe]
      exact h₂ h'

@[gcongr]
lemma width_le_width {B₁ B₂ : BohrSet G} (h : B₁ ≤ B₂) (hψ : ψ ∈ B₂.frequencies) :
    B₁.width ψ ≤ B₂.width ψ := by
  rw [le_iff_width] at h
  exact h.2 hψ

noncomputable instance : OrderTop (BohrSet G) := .lift BohrSet.ewidth (fun _ _ h => h) rfl

open scoped Classical in
noncomputable instance [Finite G] : SupSet (BohrSet G) where
  sSup B := {
    frequencies := {ψ | ⨆ i ∈ B, i.ewidth ψ < ⊤},
    ewidth ψ := ⨆ i ∈ B, ewidth i ψ
    mem_frequencies := by simp
  }

lemma iInf_lt_top {α β : Type*} [CompleteLattice β] {S : Set α} {f : α → β} :
    (⨅ i ∈ S, f i) < ⊤ ↔ ∃ i ∈ S, f i < ⊤ := by
  simp [lt_top_iff_ne_top]

open scoped Classical in
noncomputable instance [Finite G] : InfSet (BohrSet G) where
  sInf B := {
    frequencies := {ψ | ∃ i ∈ B, i.ewidth ψ < ⊤},
    ewidth ψ := ⨅ i ∈ B, ewidth i ψ
    mem_frequencies := by simp
  }

noncomputable def minimalAxioms [Finite G] :
    CompletelyDistribLattice.MinimalAxioms (BohrSet G) :=
  ewidth_injective.completelyDistribLatticeMinimalAxioms .of BohrSet.ewidth
    .rfl .rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun B ↦ by ext ψ; simp [iSup_apply]; rfl)
    (fun B ↦ by ext ψ; simp [iInf_apply]; rfl)
    rfl
    rfl

noncomputable instance [Finite G] : CompletelyDistribLattice (BohrSet G) :=
  .ofMinimalAxioms BohrSet.minimalAxioms

/-! ### Width, frequencies, rank -/

/-- The cardinality rank of a Bohr set is its number of frequencies. -/
def cardRank (B : BohrSet G) : ℕ := #B.frequencies

@[simp] lemma card_frequencies (B : BohrSet G) : #B.frequencies = B.cardRank := by rfl

/-- The dimension rank of a Bohr set is the sum of the dimensions of its frequencies. -/
noncomputable def dimRank (B : BohrSet G) : ℕ := ∑ ψ ∈ B.frequencies, Module.finrank ℂ ψ.E

/-- The squared dimension rank of a Bohr set is the sum of the squares of the dimensions of its
frequencies. -/
noncomputable def dimSqRank (B : BohrSet G) : ℕ := ∑ ψ ∈ B.frequencies, Module.finrank ℂ ψ.E ^ 2

lemma cardRank_le_dimRank : B.cardRank ≤ B.dimRank := by
  rw [← card_frequencies, Finset.card_eq_sum_ones, dimRank]
  gcongr with ψ
  rw [Nat.one_le_iff_ne_zero, ← pos_iff_ne_zero, Module.finrank_pos_iff]
  infer_instance

/-! ### Dilation -/

section smul
variable {ρ : ℝ}

lemma nnreal_smul_lt_top {x : ℝ≥0} {y : ℝ≥0∞} (hy : y < ⊤) : x • y < ⊤ :=
  ENNReal.mul_lt_top (by simp) hy

set_option backward.isDefEq.respectTransparency false in
lemma nnreal_smul_lt_top_iff {x : ℝ≥0} {y : ℝ≥0∞} (hx : x ≠ 0) : x • y < ⊤ ↔ y < ⊤ := by
  constructor
  case mpr => exact nnreal_smul_lt_top
  case mp =>
    intro h
    by_contra hy
    simp only [top_le_iff, not_lt] at hy
    simp [hy, ENNReal.smul_top, hx] at h

lemma nnreal_smul_ne_top {x : ℝ≥0} {y : ℝ≥0∞} (hy : y ≠ ⊤) : x • y ≠ ⊤ :=
  ENNReal.mul_ne_top (by simp) hy

set_option backward.isDefEq.respectTransparency false in
lemma nnreal_smul_ne_top_iff {x : ℝ≥0} {y : ℝ≥0∞} (hx : x ≠ 0) : x • y ≠ ⊤ ↔ y ≠ ⊤ := by
  constructor
  case mpr => exact nnreal_smul_ne_top
  case mp =>
    intro h
    by_contra hy
    simp [hy, ENNReal.smul_top, hx] at h

noncomputable instance instSMul : SMul ℝ (BohrSet G) where
  smul ρ B := BohrSet.mk B.frequencies
      (fun ψ => if ψ ∈ B.frequencies then Real.nnabs ρ * B.ewidth ψ else ⊤) fun ψ => by
        simp only [lt_top_iff_ne_top, ite_ne_right_iff, iff_self_and]
        intro hψ
        refine ENNReal.mul_ne_top (by simp) ?_
        rwa [←lt_top_iff_ne_top, ←mem_frequencies]

@[simp] lemma frequencies_smul (ρ : ℝ) (B : BohrSet G) : (ρ • B).frequencies = B.frequencies := rfl
@[simp] lemma cardRank_smul (ρ : ℝ) (B : BohrSet G) : (ρ • B).cardRank = B.cardRank := by rfl
@[simp] lemma dimRank_smul (ρ : ℝ) (B : BohrSet G) : (ρ • B).dimRank = B.dimRank := by rfl

@[simp] lemma ewidth_smul (ρ : ℝ) (B : BohrSet G) (ψ) :
    (ρ • B).ewidth ψ = if ψ ∈ B.frequencies then Real.nnabs ρ * B.ewidth ψ else ⊤ := rfl

@[simp] lemma width_smul_apply (ρ : ℝ) (B : BohrSet G) (ψ) :
    (ρ • B).width ψ = Real.nnabs ρ * B.width ψ := by
  rw [width, ewidth_smul]; split <;> simp [← coe_width, width_eq_zero_of_not_mem_frequencies, *]

lemma width_smul (ρ : ℝ) (B : BohrSet G) : (ρ • B).width = Real.nnabs ρ • B.width := by
  ext ψ
  simp [width_smul_apply]

noncomputable instance instMulAction : MulAction ℝ (BohrSet G) where
  one_smul B := by ext <;> simp
  mul_smul ρ φ B := by ext <;> simp [mul_assoc]

end smul

-- Note it is not sufficient to say B.width = 0.
lemma eq_singleton_one_of_ewidth_eq_zero {B : BohrSet G} (h : B.ewidth = 0) :
    B.chordSet = {1} := by
  rw [Set.eq_singleton_iff_unique_mem]
  simp only [mem_chordSet_iff_nnnorm_width, map_one,
    LinearIsometryEquiv.toContinuousLinearEquiv_one,
    ContinuousLinearEquiv.toContinuousLinearMap_one, sub_self, nnnorm_zero, zero_le, implies_true,
    true_and]
  intro x hx
  by_contra!
  sorry
  -- rw [←AddChar.exists_apply_ne_zero] at this
  -- obtain ⟨ψ, hψ⟩ := this
  -- apply hψ
  -- have hψ' : ψ ∈ B.frequencies := by simp [B.mem_frequencies, h]
  -- specialize hx hψ'
  -- rwa [B.width_def, h, Pi.zero_apply, ENNReal.toNNReal_zero, nonpos_iff_eq_zero, nnnorm_eq_zero,
  --   sub_eq_zero, eq_comm] at hx

lemma chordSet_eq_top_of_two_le_width {B : BohrSet G} (h : ∀ ψ, 2 ≤ B.width ψ) :
    B.chordSet = Set.univ := by
  simp only [Set.eq_univ_iff_forall, mem_chordSet_iff_nnnorm_width]
  intro i ψ _
  grw [nnnorm_sub_le, ← h]
  norm_num

@[gcongr] lemma chordSet_mono {B₁ B₂ : BohrSet G} (h : B₁ ≤ B₂) : B₁.chordSet ⊆ B₂.chordSet :=
  fun _ hx ψ => (hx ψ).trans (h ψ)

lemma chordSet_monotone : Monotone (chordSet : BohrSet G → Set G) := fun _ _ => chordSet_mono

open Pointwise

lemma chordSet_mul_chordSet_subset {B₁ B₂ B₃ : BohrSet G} (h : B₁.ewidth + B₂.ewidth ≤ B₃.ewidth) :
    B₁.chordSet * B₂.chordSet ⊆ B₃.chordSet := by
  intro x
  simp only [mem_chordSet_iff_nnnorm_ewidth, Set.mem_mul, forall_exists_index, and_imp]
  rintro x hx y hy rfl ψ
  rw [map_mul]
  have : ‖1 - (ψ x : ψ.E →L[ℂ] ψ.E) * ψ y‖₊ ≤ ‖1 - (ψ x : ψ.E →L[ℂ] ψ.E)‖₊ + _ :=
    nnnorm_sub_mul_le (by simp)
  rw [← ENNReal.coe_le_coe, ENNReal.coe_add] at this
  exact this.trans <| (h _).trans' <| add_le_add (hx _) (hy _)

lemma chordSet_smul_add_chordSet_smul_subset {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    (ρ₁ • B).chordSet * (ρ₂ • B).chordSet ⊆ ((ρ₁ + ρ₂) • B).chordSet :=
  chordSet_mul_chordSet_subset fun ψ => by
    simp only [Pi.add_apply, ewidth_smul]; split <;> simp [add_nonneg, add_mul, *]

end Group

section CommGroup
variable [CommGroup G] {B : BohrSet G}

variable (B) in
@[simp] lemma dimRank_eq_cardRank : B.dimRank = B.cardRank := by simp [dimRank]

variable (B) in
@[simp] lemma dimSqRank_eq_cardRank : B.dimSqRank = B.cardRank := by simp [dimSqRank]

end CommGroup
end BohrSet
