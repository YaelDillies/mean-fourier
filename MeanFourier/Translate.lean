/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Util.Notation3

/-!
# Translating functions
-/

public section

variable {G α : Type*} [Group G]

/-- Left-translation of a function: `τ_[x] f y := f (x⁻¹ * y)`. -/
@[expose]
def translate (x : G) (f : G → α) : G → α := fun y ↦ f (x⁻¹ * y)

@[inherit_doc translate] notation3 "τ_[" x "]" => translate x

@[simp] lemma translate_apply (x : G) (f : G → α) (y : G) : τ_[x] f y = f (x⁻¹ * y) := rfl

@[simp] lemma translate_one (f : G → α) : τ_[1] f = f := by ext; simp
@[simp] lemma translate_translate (x y : G) (f : G → α) : τ_[x] (τ_[y] f) = τ_[x * y] f := by
  ext; simp [mul_assoc]
