/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Data.Set.Basic
public import Mathlib.Util.Notation3
public import MeanFourier.Mathlib.Topology.Bornology.Basic

/-!
# Translating functions
-/

public section

namespace Function
variable {G α M : Type*} [Group G] {x : G} {f : G → α}

/-- Left-translation of a function: `τ_[x] f y := f (x⁻¹ * y)`. -/
@[expose]
def translate (x : G) (f : G → α) : G → α := fun y ↦ f (x⁻¹ * y)

@[inherit_doc translate] notation3 "τ_[" x "]" => translate x

@[simp] lemma translate_apply (x : G) (f : G → α) (y : G) : τ_[x] f y = f (x⁻¹ * y) := rfl

@[simp] lemma translate_one (f : G → α) : τ_[1] f = f := by ext; simp
@[simp] lemma translate_translate (x y : G) (f : G → α) : τ_[x] (τ_[y] f) = τ_[x * y] f := by
  ext; simp [mul_assoc]

-- TODO: Move the `attribute [local push] Function.const_def` from `Mathlib.Order.ScottContinuity`
-- to an earlier file.
@[to_fun (attr := simp) translate_fun_const]
lemma translate_const (x : G) (a : α) : τ_[x] (const G a) = const G a := rfl

@[to_additive (attr := simp) (dont_translate := G)]
lemma translate_one_fun [One M] (x : G) : τ_[x] (1 : G → M) = 1 := rfl

@[to_additive (attr := simp) (dont_translate := G)]
lemma translate_mul_fun [Mul M] (x : G) (f g : G → M) : τ_[x] (f * g) = τ_[x] f * τ_[x] g := rfl

@[simp] lemma range_translate (x : G) (f : G → α) : Set.range (τ_[x] f) = .range f := by
  ext a; exact (Equiv.mulLeft x⁻¹).exists_congr (by simp)

end Function

namespace Bornology
variable {G X : Type*} [Group G] [Bornology X] {x : G} {f : G → X}

@[simp] lemma isBddFun_translate : IsBddFun (τ_[x] f) ↔ IsBddFun f := by simp [IsBddFun]

protected alias ⟨_, IsBddFun.translate⟩ := isBddFun_translate

end Bornology

open scoped Pointwise

@[simp] lemma translate_add_right {β : Type*} [Add β] (x : G) (f g : G → β) :
    τ_[x] (f + g) = τ_[x] f + τ_[x] g := rfl

variable (f) in
abbrev translates : Set (G → α) := Set.range fun x : G ↦ τ_[x] f

lemma mem_translates {g : G → α} : g ∈ translates f ↔ ∃ x : G, τ_[x] f = g := Iff.rfl

lemma translate_mem_translates (f : G → α) (x : G) : τ_[x] f ∈ translates f := ⟨x, rfl⟩

lemma self_mem_translates (f : G → α) : f ∈ translates f := ⟨1, Function.translate_one f⟩
