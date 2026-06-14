/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Interval.Set.Basic
public import MeanFourier.Mathlib.Data.Set.Card

/-!
# VC dimension

This file defines the VC dimension of set families.
-/

public section

variable {α : Type*}

section SemilatticeInf
variable [SemilatticeInf α] {𝒜 ℬ : Set α} {A B : α}

/-- A set family `𝒜` shatters a set `A` if all subsets of `A` can be obtained as the intersection
of `A` with some element of the set family. We also say that `A` is *traced* by `𝒜`. -/
@[expose]
def Shatters (𝒜 : Set α) (A : α) : Prop := ∀ ⦃B⦄, B ≤ A → ∃ C ∈ 𝒜, A ⊓ C = B

lemma Shatters.mono (h : 𝒜 ⊆ ℬ) (h𝒜 : Shatters 𝒜 A) : Shatters ℬ A :=
  fun _B hBA ↦ let ⟨C, hC, hCB⟩ := h𝒜 hBA; ⟨C, h hC, hCB⟩

lemma Shatters.anti (h : A ≤ B) (hB : Shatters 𝒜 B) : Shatters 𝒜 A := fun C hCA ↦ by
  obtain ⟨D, hD, rfl⟩ := hB (hCA.trans h); exact ⟨D, hD, inf_congr_right hCA <| inf_le_of_left_le h⟩

lemma Shatters.exists_ge (h : Shatters 𝒜 A) : ∃ B ∈ 𝒜, A ≤ B := by simpa using h le_rfl

lemma Shatters.of_forall_le (h : ∀ B ≤ A, B ∈ 𝒜) : Shatters 𝒜 A :=
  fun B hBA ↦ ⟨B, h _ hBA, inf_eq_right.2 hBA⟩

protected lemma Shatters.nonempty (h : Shatters 𝒜 A) : 𝒜.Nonempty :=
  let ⟨B, hB, _⟩ := h le_rfl; ⟨B, hB⟩

protected lemma Shatters.le_iff (h : Shatters 𝒜 A) : B ≤ A ↔ ∃ C ∈ 𝒜, A ⊓ C = B :=
  ⟨fun ht ↦ h ht, by rintro ⟨u, _, rfl⟩; exact inf_le_left⟩

lemma shatters_iff_image_inf_eq_Iic : Shatters 𝒜 A ↔ (A ⊓ ·) '' 𝒜 = .Iic A := by
  aesop (add simp [Set.ext_iff, Shatters])

protected lemma Shatters.univ : Shatters .univ A := .of_forall_le <| by simp

@[simp] lemma shatters_bot [OrderBot α] : Shatters 𝒜 ⊥ ↔ 𝒜.Nonempty :=
  ⟨Shatters.nonempty, fun ⟨A, hA⟩ B hB ↦ ⟨A, hA, by simpa [eq_comm] using hB⟩⟩

@[simp] lemma shatters_top [OrderTop α] : Shatters 𝒜 ⊤ ↔ 𝒜 = .univ := by
  simp [shatters_iff_image_inf_eq_Iic]

end SemilatticeInf

section BooleanAlgebra
variable [BooleanAlgebra α] {𝒜 : Set α} {A : α}

lemma Shatters.preimage_compl (hA : Shatters 𝒜 A) : Shatters ((·ᶜ) ⁻¹' 𝒜) A := by
  rintro B hBA
  obtain ⟨C, hC, hABC⟩ : ∃ C ∈ 𝒜, A ⊓ C = A \ B := hA sdiff_le
  exact ⟨Cᶜ, by simpa, by simpa [← sdiff_eq, hBA] using congr(A \ $hABC)⟩

@[simp] lemma shatters_preimage_compl : Shatters ((·ᶜ) ⁻¹' 𝒜) A ↔ Shatters 𝒜 A where
  mp hA := by simpa [Set.preimage_preimage] using hA.preimage_compl
  mpr := .preimage_compl

@[simp] lemma shatters_image_compl : Shatters ((·ᶜ) '' 𝒜) A ↔ Shatters 𝒜 A := by
  simp [← Set.preimage_compl_eq_image_compl]

alias ⟨_, Shatters.image_compl⟩ := shatters_image_compl

end BooleanAlgebra

section Finset
variable [DecidableEq α] {𝒜 ℬ : Finset (Finset α)}

instance : DecidablePred (Shatters (𝒜 : Set (Finset α))) :=
  fun _s ↦ Finset.decidableForallOfDecidableSubsets

end Finset

section Set
variable {m n d d₁ d₂ : ℕ} {𝒜 ℬ : Set (Set α)} {A : Set α}

open scoped Finset

variable (n d 𝒜) in
/-- A set family has growth at most `d` at level `n` if it cuts out at most `d` sets from any set
of size at most `n`. -/
@[expose]
noncomputable def HasVCGrowthLE : Prop := ∀ ⦃A : Finset α⦄, #A ≤ n → ((↑A ∩ ·) '' 𝒜).ncard ≤ d

@[gcongr]
lemma HasVCGrowthLE.subset (h : 𝒜 ⊆ ℬ) : HasVCGrowthLE n d ℬ → HasVCGrowthLE n d 𝒜 := by
  grw [HasVCGrowthLE, HasVCGrowthLE, h]; exacts [id, A.finite_toSet.powerset.subset (by grind)]

@[gcongr]
lemma HasVCGrowthLE.mono (h : m ≤ n) : HasVCGrowthLE n d 𝒜 → HasVCGrowthLE m d 𝒜 := by
  grw [HasVCGrowthLE, HasVCGrowthLE, h]; exact id

@[gcongr]
lemma HasVCGrowthLE.anti (h : d₁ ≤ d₂) : HasVCGrowthLE n d₁ 𝒜 → HasVCGrowthLE n d₂ 𝒜 := by
  grw [HasVCGrowthLE, HasVCGrowthLE, h]; exact id

protected lemma HasVCGrowthLE.union (h𝒜 : HasVCGrowthLE n d₁ 𝒜) (hℬ : HasVCGrowthLE n d₂ ℬ) :
    HasVCGrowthLE n (d₁ + d₂) (𝒜 ∪ ℬ) := by
  rintro A hA
  grw [Set.image_union, Set.ncard_union_le, h𝒜 hA, hℬ hA]

lemma HasVCGrowthLE.image2_inter (h𝒜 : HasVCGrowthLE n d₁ 𝒜) (hℬ : HasVCGrowthLE n d₂ ℬ) :
    HasVCGrowthLE n (d₁ * d₂) (.image2 (· ∩ ·) 𝒜 ℬ) := by
  rintro A hA
  grw [Set.image_image2_distrib (Set.inter_inter_distrib_left _), Set.ncard_image2_le, h𝒜 hA,
    hℬ hA] <;> exact A.finite_toSet.powerset.subset <| by grind

/-- A set family `𝒜` has VC dimension at most `d` if all the sets it shatters have size at most
`d`. -/
@[expose]
def HasVCDimLE (d : ℕ) (𝒜 : Set (Set α)) : Prop := ∀ ⦃A : Finset α⦄, Shatters 𝒜 A → #A ≤ d

@[gcongr]
lemma HasVCDimLE.anti (hℬ𝒜 : ℬ ⊆ 𝒜) (hd : HasVCDimLE d 𝒜) : HasVCDimLE d ℬ :=
  fun _A hA ↦ hd <| hA.mono hℬ𝒜

@[gcongr]
lemma HasVCDimLE.mono (hd : d₁ ≤ d₂) (h𝒜 : HasVCDimLE d₁ 𝒜) : HasVCDimLE d₂ 𝒜 :=
  fun _A hA ↦ (h𝒜 hA).trans hd

end Set
