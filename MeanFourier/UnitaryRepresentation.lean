/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.RepresentationTheory.Basic
public import MeanFourier.Mathlib.Analysis.InnerProductSpace.Adjoint

public section

namespace Representation
variable {𝕜 G E : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- A representation `ρ` on a finite-dimensional inner product space is unitary if `ρ x` is a
unitary operator for each `x`. -/
@[expose]
def IsUnitary (ρ : Representation 𝕜 G E) : Prop := ∀ x, ρ x ∈ unitary (E →ₗ[𝕜] E)

@[simp] protected lemma IsUnitary.trivial : IsUnitary (trivial 𝕜 G E) := by simp [IsUnitary]

end Representation
