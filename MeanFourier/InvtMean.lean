/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import AddCombi.Mathlib.Algebra.Notation.Indicator
public import Mathlib.Analysis.Complex.Basic

public section

open scoped ComplexOrder Indicator

variable {G : Type*} [Group G]

variable (G) in
structure InvtMean where
  IsMeasFun : (G → ℂ) → Prop
  isMeasFun_const (z : ℂ) : IsMeasFun fun _ ↦ z
  isMeasFun_translate (g : G) (f : G → ℂ) (hf : IsMeasFun f) : IsMeasFun fun h ↦ f (g⁻¹ * h)
  bdd_of_isMeasFun (f : G → ℂ) (hf : IsMeasFun f) : ∃ C, ∀ g, ‖f g‖ ≤ C
  toFun : (G → ℂ) → ℂ
  map_zero : toFun 0 = 0
  map_add (f₁ : G → ℂ) (h₁ : IsMeasFun f₁) (f₂ : G → ℂ) (h₂ : IsMeasFun f₂) :
    toFun (f₁ + f₂) = toFun f₁ + toFun f₂
  map_smul (f : G → ℂ) (hf : IsMeasFun f) (z : ℂ) : toFun (z • f) = z • toFun f
  map_nonneg (f : G → ℂ) (hf₀ : 0 ≤ f) : 0 ≤ toFun f
  map_translate (f : G → ℂ) (hf : IsMeasFun f) (g : G) : toFun (fun h ↦ f (g⁻¹ * h)) = toFun f

namespace InvtMean
variable {m : InvtMean G} {f : G → ℂ} {A : Set G} {g : G} {z : ℂ}

instance : CoeFun (InvtMean G) fun _ ↦ (G → ℂ) → ℂ where coe := toFun

attribute [fun_prop] IsMeasFun

@[fun_prop, simp] lemma IsMeasFun.const : m.IsMeasFun fun _ ↦ z := m.isMeasFun_const _
@[fun_prop, simp] lemma IsMeasFun.natCast {n : ℕ} : m.IsMeasFun n := .const
@[fun_prop, simp] lemma IsMeasFun.intCast {n : ℤ} : m.IsMeasFun n := .const

@[fun_prop, simp] protected lemma IsMeasFun.zero : m.IsMeasFun 0 := .const
@[fun_prop, simp] protected lemma IsMeasFun.one : m.IsMeasFun 0 := .const

@[fun_prop, simp]
protected lemma IsMeasFun.ofNat {n : ℕ} [n.AtLeastTwo] : m.IsMeasFun ofNat(n) := .const

lemma IsMeasFun.translate (hf : m.IsMeasFun f) : m.IsMeasFun fun h ↦ f (g⁻¹ * h) :=
  m.isMeasFun_translate _ _ hf

lemma IsMeasFun.bdd (hf : m.IsMeasFun f) : ∃ C, ∀ g, ‖f g‖ ≤ C := m.bdd_of_isMeasFun _ hf

variable (m) in
def real (f : G → ℝ) : ℝ := (m fun g ↦ f g).re

instance : CoeFun (InvtMean G) fun _ ↦ (G → ℝ) → ℝ where coe := real

variable (m) in
def l2 : Set (G → ℂ) := {f | m.IsMeasFun fun g ↦ ‖f g‖ ^ 2}

notation3 "L^2(" m ")" => l2 m

variable (m f) in
noncomputable def l2Norm : ℝ := √(m fun g ↦ ‖f g‖ ^ 2)

variable (m A) in
@[simp] lemma l2Norm_indicator_one : m.l2Norm 𝟭_[A] = √(m 𝟭_[A]) := by
  classical simp [l2Norm, Set.indicator_apply, apply_ite, norm_one, real]

variable (m A) in
def IsMeasSet : Prop := m.IsMeasFun 𝟭_[A]

end InvtMean
