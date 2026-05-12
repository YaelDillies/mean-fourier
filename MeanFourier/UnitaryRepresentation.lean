/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.RepresentationTheory.Basic
public import MeanFourier.Mathlib.Analysis.Normed.Operator.LinearIsometry
public import MeanFourier.Mathlib.Topology.Algebra.Module.Equiv

public section

variable {𝕜 G E : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (𝕜 G E) in
abbrev UnitaryRepresentation : Type _ := G →* E ≃ₗᵢ[𝕜] E

namespace UnitaryRepresentation

@[expose]
noncomputable def toRepresentation (ρ : UnitaryRepresentation 𝕜 G E) : Representation 𝕜 G E where
  toFun g := ρ g
  map_one' := by simp
  map_mul' := by simp

variable (𝕜 G E) in
abbrev trivial : UnitaryRepresentation 𝕜 G E := 1

end UnitaryRepresentation
