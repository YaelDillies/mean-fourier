/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import AddCombi.Mathlib.Algebra.Notation.Indicator
public import Mathlib.Analysis.Complex.Basic
public import MeanFourier.Mathlib.Analysis.Normed.Group.Pointwise
public import MeanFourier.Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import MeanFourier.Translate

/-!
# Invariant means
-/

public section

open Bornology
open scoped ComplexOrder Indicator

variable {G 𝕜 E R : Type*} [Group G] [RCLike 𝕜] [NormedAddCommGroup E] [PartialOrder E]
  [NormedSpace 𝕜 E]

variable (G 𝕜 E) [NormedAddCommGroup E] [PartialOrder E] [NormedSpace 𝕜 E] in
structure InvtMean where
  IsMeasFun : (G → E) → Prop
  isMeasFun_const (z : E) : IsMeasFun fun _ ↦ z := by fun_prop
  isMeasFun_add (f : G → E) (hf : IsMeasFun f) (g : G → E) (hg : IsMeasFun g) :
    IsMeasFun (f + g) := by fun_prop
  isMeasFun_smul (c : 𝕜) (f : G → E) (hf : IsMeasFun f) : IsMeasFun (c • f) := by fun_prop
  isMeasFun_translate (x : G) (f : G → E) (hf : IsMeasFun f) : IsMeasFun (τ_[x] f) := by fun_prop
  isBddFun_of_isMeasFun (f : G → E) (hf : IsMeasFun f) : IsBddFun f := by fun_prop
  toFun : (G → E) → E
  map_zero : toFun 0 = 0
  map_add (f : G → E) (hf : IsMeasFun f) (g : G → E) (hg : IsMeasFun g) :
    toFun (f + g) = toFun f + toFun g
  map_smul (f : G → E) (hf : IsMeasFun f) (c : 𝕜) : toFun (c • f) = c • toFun f
  map_nonneg (f : G → E) (hf₀ : 0 ≤ f) (hf : IsMeasFun f) : 0 ≤ toFun f
  map_translate (f : G → E) (hf : IsMeasFun f) (x : G) : toFun (τ_[x] f) = toFun f

namespace InvtMean
section NormedAddCommGroup
variable {m : InvtMean G 𝕜 E} {f g : G → E} {A : Set G} {x : G} {z : E}

instance : CoeFun (InvtMean G 𝕜 E) fun _ ↦ (G → E) → E where coe := toFun

initialize_simps_projections InvtMean (toFun → apply, as_prefix IsMeasFun)

attribute [fun_prop] IsMeasFun

@[fun_prop, simp] lemma IsMeasFun.const : m.IsMeasFun fun _ ↦ z := m.isMeasFun_const _

@[fun_prop, simp] protected lemma IsMeasFun.zero : m.IsMeasFun 0 := .const

@[fun_prop]
protected lemma IsMeasFun.add (hf : m.IsMeasFun f) (hg : m.IsMeasFun g) : m.IsMeasFun (f + g) :=
  m.isMeasFun_add _ hf _ hg

protected lemma IsMeasFun.translate (hf : m.IsMeasFun f) : m.IsMeasFun (τ_[x] f) :=
  m.isMeasFun_translate _ _ hf

@[fun_prop]
lemma IsMeasFun.isBddFun (hf : m.IsMeasFun f) : IsBddFun f := m.isBddFun_of_isMeasFun _ hf

end NormedAddCommGroup

section NormedRing
variable [NormedRing R] [PartialOrder R] [NormedSpace 𝕜 R] {m : InvtMean G 𝕜 R}

@[fun_prop, simp] lemma IsMeasFun.natCast {n : ℕ} : m.IsMeasFun n := .const
@[fun_prop, simp] lemma IsMeasFun.intCast {n : ℤ} : m.IsMeasFun n := .const
@[fun_prop, simp] protected lemma IsMeasFun.one : m.IsMeasFun 1 := .const

@[fun_prop, simp]
protected lemma IsMeasFun.ofNat {n : ℕ} [n.AtLeastTwo] : m.IsMeasFun ofNat(n) := .const

variable (m A) in
/-- A set `A` is `m`-measurable if `𝟭_[A]` is `m`-measurable. -/
@[expose] def IsMeasSet : Prop := m.IsMeasFun 𝟭_[A]

end NormedRing

section Complex
variable {m : InvtMean G ℂ ℂ} {f g : G → ℂ}

variable (m) in
@[expose]
def real (f : G → ℝ) : ℝ := (m fun g ↦ f g).re

@[simp] lemma real_mk (IsMeasFun isMeasFun_const isMeasFun_add isMeasFun_smul isMeasFun_translate
    isBddFun_of_isMeasFun toFun map_zero map_add map_smul map_nonneg map_translate) (f : G → ℝ) :
    (mk IsMeasFun isMeasFun_const isMeasFun_add isMeasFun_smul isMeasFun_translate
      isBddFun_of_isMeasFun toFun map_zero map_add map_smul map_nonneg map_translate).real f
      = (toFun fun g ↦ f g).re := rfl

instance : CoeFun (InvtMean G ℂ ℂ) fun _ ↦ (G → ℝ) → ℝ where coe := real

variable (m) in
def l2 : Set (G → E) := {f | m.IsMeasFun fun g ↦ ‖f g‖ ^ 2}

notation3 "L^2(" m ")" => l2 m

variable (m f) in
noncomputable def l2Norm : ℝ := √(m fun g ↦ ‖f g‖ ^ 2)

variable (m A) in
@[simp] lemma l2Norm_indicator_one : m.l2Norm 𝟭_[A] = √(m 𝟭_[A]) := by
  classical simp [l2Norm, Set.indicator_apply, apply_ite, norm_one, real]

end Complex
end InvtMean
