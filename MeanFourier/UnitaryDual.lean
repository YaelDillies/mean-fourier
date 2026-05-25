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

universe u
variable {𝕜 : Type u} {ι G : Type*} [RCLike 𝕜]

variable (𝕜 G) in
def UnitaryDual [Group G] : Type _ :=
  Skeleton <| ObjectProperty.FullSubcategory
    fun ψ : UnitaryRep.{u} 𝕜 G ↦ ψ.ρ.toRepresentation.IsIrreducible

namespace UnitaryDual
section Group
variable [Group G] {ψ : UnitaryDual 𝕜 G}

variable (ψ) in
protected def E : Type _ := ψ.out.1.E

@[no_expose] instance : NormedAddCommGroup ψ.E := ψ.out.1.normedAddCommGroup
@[no_expose] instance : InnerProductSpace 𝕜 ψ.E := ψ.out.1.innerProductSpace

instance : CompleteSpace ψ.E := ψ.out.1.completeSpace
instance : FiniteDimensional 𝕜 ψ.E := sorry

variable (ψ) in
protected def ρ : UnitaryRepresentation 𝕜 G ψ.E := ψ.out.1.ρ

@[simp] lemma isIrreducible_ρ : ψ.ρ.toRepresentation.IsIrreducible := ψ.out.2

instance : Nontrivial ψ.E := sorry

instance : CoeFun (UnitaryDual 𝕜 G) fun ψ ↦ G → ψ.E ≃ₗᵢ[𝕜] ψ.E where coe ψ := ψ.ρ

instance : DecidableEq (UnitaryDual 𝕜 G) := Classical.decEq _

-- TODO: Generalise the universe level using finite dimensionality of `E`
def ofUnitaryRepresentation {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] (ρ : UnitaryRepresentation 𝕜 G E)
    (hρ : ρ.toRepresentation.IsIrreducible) : UnitaryDual 𝕜 G :=
  toSkeleton ⟨.of ρ, hρ⟩

instance [Finite G] : Fintype (UnitaryDual ℂ G) := sorry

end Group

section CommGroup
variable [CommGroup G] {ψ : UnitaryDual ℂ G}

variable (ψ) in
@[simp] lemma finrank_E_eq_one : Module.finrank ℂ ψ.E = 1 :=
  UnitaryRepresentation.finrank_eq_one_of_isIrreducible isIrreducible_ρ

end CommGroup
end UnitaryDual
