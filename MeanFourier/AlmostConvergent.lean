/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Module.Basic
public import MeanFourier.Translate

/-!
# Almost-convergent functions
-/

public section

open Bornology

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [NormedSpace ℝ E] {f : G → E} {z : E}

variable (f) in
/-- A function `f` from a group `G` to a normed space `E` is almost-convergent if if it is bounded
and the closure in the L^∞ norm of the convex hull of its translates contains a unique constant
function. -/
@[mk_iff, fun_prop]
structure IsAlmostConvergent : Prop where
  isBddFun : IsBddFun f
  existsUnique_const_mem_closure_convexHull :
    ∃! z, Function.const G z ∈ closure (convexHull ℝ (Set.range fun x ↦ τ_[x] f))

attribute [fun_prop] IsAlmostConvergent.isBddFun

@[to_fun (attr := simp, fun_prop)]
protected lemma IsAlmostConvergent.const : IsAlmostConvergent (Function.const G z) := by
  simp [isAlmostConvergent_iff]

@[simp, fun_prop]
protected lemma IsAlmostConvergent.zero : IsAlmostConvergent (0 : G → E) := .const
