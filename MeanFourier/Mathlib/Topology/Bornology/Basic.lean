/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Int.Cast.Pi
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Order.ScottContinuity
public import Mathlib.Topology.Bornology.Basic

/-!
# Bounded functions
-/

public section

variable {α X : Type*} [Bornology X]

namespace Bornology
variable {x : X} {f : α → X}

@[expose, fun_prop] def IsBddFun (f : α → X) : Prop := IsBounded (.range f)

-- TODO: Move the `attribute [local push] Function.const_def` from `Mathlib.Order.ScottContinuity`
-- to an earlier file.
@[to_fun (attr := simp, fun_prop)]
protected lemma IsBddFun.const : IsBddFun (Function.const α x) := (Set.finite_range_const).isBounded

@[to_additive (attr := simp, fun_prop)]
protected lemma IsBddFun.one [One X] : IsBddFun (1 : α → X) := .const

@[simp, fun_prop]
protected lemma IsBddFun.natCast [NatCast X] {n : ℕ} : IsBddFun (n : α → X) := .const

@[simp, fun_prop]
protected lemma IsBddFun.ofNat [NatCast X] {n : ℕ} [n.AtLeastTwo] : IsBddFun (ofNat(n) : α → X) :=
  .const

@[simp, fun_prop]
protected lemma IsBddFun.intCast [IntCast X] {n : ℤ} : IsBddFun (n : α → X) := .const

@[fun_prop] lemma IsBddFun.of_finite [Finite α] : IsBddFun f := (Set.finite_range _).isBounded

end Bornology
