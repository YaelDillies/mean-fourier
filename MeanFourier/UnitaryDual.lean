/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import MeanFourier.UnitaryRep

/-!
# The unitary dual of a group
-/

public noncomputable section

open CategoryTheory

universe w
variable {𝕜 : Type w} {ι G : Type*} [RCLike 𝕜] [Group G]

variable (𝕜 G) in
def UnitaryDual : Type _ :=
  Skeleton <| ObjectProperty.FullSubcategory
    fun ψ : UnitaryRep 𝕜 G ↦ ψ.ρ.toRepresentation.IsIrreducible

namespace UnitaryDual
variable {ψ : UnitaryDual 𝕜 G}

def ofUnitaryRepresentation {E : Type w} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] (ρ : UnitaryRepresentation 𝕜 G E)
    (hρ : ρ.toRepresentation.IsIrreducible) : UnitaryDual 𝕜 G :=
  toSkeleton ⟨.of ρ, hρ⟩

variable (ψ) in
protected def E : Type _ := ψ.out.1.E

@[no_expose] instance : NormedAddCommGroup ψ.E := ψ.out.1.normedAddCommGroup
@[no_expose] instance : InnerProductSpace 𝕜 ψ.E := ψ.out.1.innerProductSpace

instance : FiniteDimensional 𝕜 ψ.E := ψ.out.1.finiteDimensional

variable (ψ) in
protected def ρ : UnitaryRepresentation 𝕜 G ψ.E := ψ.out.1.ρ

@[simp] lemma isIrreducible_ρ : ψ.ρ.toRepresentation.IsIrreducible := ψ.out.2

instance : Nontrivial ψ.E := sorry

instance : CoeFun (UnitaryDual 𝕜 G) fun ψ ↦ G → ψ.E ≃ₗᵢ[𝕜] ψ.E where coe ψ := ψ.ρ

instance : DecidableEq (UnitaryDual 𝕜 G) := Classical.decEq _

instance [Finite G] : Fintype (UnitaryDual ℂ G) := sorry

end UnitaryDual
