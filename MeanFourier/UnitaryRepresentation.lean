/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.RepresentationTheory.Irreducible

import Mathlib.Analysis.Complex.Polynomial.Basic

public section

variable {𝕜 G E : Type*}

section RCLike
variable [RCLike 𝕜] [Group G] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

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
end RCLike

section Complex
variable [CommGroup G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {ρ : UnitaryRepresentation ℂ G E}

namespace UnitaryRepresentation

lemma finrank_eq_one_of_isIrreducible (hρ : ρ.toRepresentation.IsIrreducible) :
    Module.finrank ℂ E = 1 := by
  have : FiniteDimensional ℂ E := sorry
  exact hρ.finrank_eq_one_of_isMulCommutative

end UnitaryRepresentation
end Complex
