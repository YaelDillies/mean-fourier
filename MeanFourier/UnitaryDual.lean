/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import MeanFourier.UnitaryRep

import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RepresentationTheory.Maschke

/-!
# The unitary dual of a group
-/

public noncomputable section

open CategoryTheory Module UnitaryRepresentation Representation
open scoped MonoidAlgebra

universe u
variable {𝕜 : Type u} {ι G : Type*} [RCLike 𝕜]

variable (𝕜 G) in
def UnitaryDual [Group G] : Type _ :=
  Skeleton <| ObjectProperty.FullSubcategory
    fun ψ : UnitaryRep.{u} 𝕜 G ↦ ψ.ρ.toRepresentation.IsIrreducible

lemma toSpanSingleton_surjective {R S : Type*} [Ring R] [AddCommGroup S] [Module R S]
    [IsSimpleModule R S] {v : S} (hv : v ≠ 0) :
    Function.Surjective (LinearMap.toSpanSingleton R S v) := by
  refine LinearMap.range_eq_top.mp <| (eq_bot_or_eq_top _).resolve_left fun h ↦ hv ?_
  have : v ∈ LinearMap.range (LinearMap.toSpanSingleton R S v) := ⟨1, one_smul R v⟩
  rwa [h, Submodule.mem_bot] at this

lemma IsSimpleModule.exists_submodule_self_linearEquiv {R S : Type*} [Ring R]
    [AddCommGroup S] [Module R S] [IsSemisimpleRing R] [IsSimpleModule R S] :
    ∃ m : Submodule R R, IsSimpleModule R ↥m ∧ Nonempty (m ≃ₗ[R] S) := by
  obtain ⟨v, hv⟩ := @exists_ne S (IsSimpleModule.nontrivial R S) 0
  set φ := LinearMap.toSpanSingleton R S v
  have : Function.Surjective φ := toSpanSingleton_surjective (R := R) hv
  obtain ⟨m, hm⟩ := exists_isCompl φ.ker
  have : m ≃ₗ[R] S :=
    (Submodule.quotientEquivOfIsCompl _ m hm).symm.trans (φ.quotKerEquivOfSurjective this)
  exact ⟨m, .congr this, ⟨this⟩⟩

lemma isotypicComponent_mem_isotypicComponents {R S : Type*} [Ring R] [AddCommGroup S] [Module R S]
    [IsSemisimpleRing R] [IsSimpleModule R S] :
    isotypicComponent R R S ∈ isotypicComponents R R := by
  obtain ⟨m, hm, ⟨e⟩⟩ := IsSimpleModule.exists_submodule_self_linearEquiv (R := R) (S := S)
  exact ⟨m, hm, e.isotypicComponent_eq.symm⟩

lemma linearEquiv_of_isotypicComponent_eq {R S₁ S₂ : Type*} [Ring R]
    [AddCommGroup S₁] [Module R S₁] [AddCommGroup S₂] [Module R S₂]
    (h : isotypicComponent R R S₁ = isotypicComponent R R S₂)
    [IsSimpleModule R S₁] [IsSimpleModule R S₂] [IsSemisimpleRing R] :
    Nonempty (S₁ ≃ₗ[R] S₂) := by
  obtain ⟨m₁, hm₁, ⟨e₁⟩⟩ := IsSimpleModule.exists_submodule_self_linearEquiv (R := R) (S := S₁)
  have : m₁ ≤ isotypicComponent R R S₂ := h ▸ le_sSup ⟨e₁⟩
  obtain ⟨e₂⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent R R _) m₁ this
  exact ⟨e₁.symm.trans e₂⟩

namespace UnitaryDual
section Group
variable [Group G] {ψ : UnitaryDual 𝕜 G}

variable (ψ) in
protected def E : Type _ := ψ.out.1.E

@[no_expose] instance : NormedAddCommGroup ψ.E := ψ.out.1.normedAddCommGroup
@[no_expose] instance : InnerProductSpace 𝕜 ψ.E := ψ.out.1.innerProductSpace

instance : CompleteSpace ψ.E := ψ.out.1.completeSpace
instance : FiniteDimensional 𝕜 ψ.E := ψ.out.1.finiteDimensional

variable (ψ) in
protected def ρ : UnitaryRepresentation 𝕜 G ψ.E := ψ.out.1.ρ

@[simp] lemma isIrreducible_ρ : ψ.ρ.toRepresentation.IsIrreducible := ψ.out.2

instance (ψ : UnitaryDual 𝕜 G) : IsSimpleModule 𝕜[G] ψ.ρ.toRepresentation.asModule :=
  (irreducible_iff_isSimpleModule_asModule _).mp isIrreducible_ρ

instance : Nontrivial ψ.E :=
  have : Nontrivial ψ.ρ.toRepresentation.asModule := IsSimpleModule.nontrivial 𝕜[G] _
  Equiv.nontrivial ψ.ρ.toRepresentation.asModuleEquiv.symm.toEquiv

instance : CoeFun (UnitaryDual 𝕜 G) fun ψ ↦ G → ψ.E ≃ₗᵢ[𝕜] ψ.E where coe ψ := ψ.ρ

instance : DecidableEq (UnitaryDual 𝕜 G) := Classical.decEq _

-- TODO: Generalise the universe level using finite dimensionality of `E`
def ofUnitaryRepresentation {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] [FiniteDimensional 𝕜 E] (ρ : UnitaryRepresentation 𝕜 G E)
    (hρ : ρ.toRepresentation.IsIrreducible) : UnitaryDual 𝕜 G :=
  toSkeleton ⟨.of ρ, hρ⟩

lemma eq_of_asModule_linearEquiv {ψ₁ ψ₂ : UnitaryDual 𝕜 G}
    (e : ψ₁.ρ.toRepresentation.asModule ≃ₗ[𝕜[G]] ψ₂.ρ.toRepresentation.asModule) :
    ψ₁ = ψ₂ := by
  have : ψ₁.ρ.toRepresentation.IsIrreducible := isIrreducible_ρ
  have : ψ₂.ρ.toRepresentation.IsIrreducible := isIrreducible_ρ
  set f := (IntertwiningMap.equivLinearMapAsModule
    (ρ := ψ₁.ρ.toRepresentation) (σ := ψ₂.ρ.toRepresentation)).symm e.toLinearMap with hf
  have h_bij : Function.Bijective f := by
    refine (IsIrreducible.bijective_or_eq_zero f).resolve_right ?_
    intro hf_zero
    have : e.toLinearMap = 0 := by
      rwa [hf_zero, eq_comm, LinearEquiv.symm_apply_eq, map_zero] at hf
    obtain ⟨v, hv⟩ :=
      @exists_ne ψ₁.ρ.toRepresentation.asModule (IsSimpleModule.nontrivial 𝕜[G] _) 0
    have : e v = 0 := congr_fun (congr_arg (↑) this) v
    exact hv (e.injective (this.trans e.map_zero.symm))
  exact skeleton_skeletal _
    ⟨(fromSkeleton _).preimageIso <|
      (ObjectProperty.ι _).preimageIso (X := ψ₁.out) (Y := ψ₂.out)
        (UnitaryRep.mkIso (f.ofBijective h_bij))⟩

instance [Finite G] : Finite (UnitaryDual ℂ G) := by
  classical
  cases nonempty_fintype G
  have : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩
  refine Finite.of_injective
    (fun ψ ↦ (⟨_, isotypicComponent_mem_isotypicComponents
      (S := ψ.ρ.toRepresentation.asModule)⟩ : isotypicComponents ℂ[G] ℂ[G])) ?_
  intro ψ₁ ψ₂ h
  rw [Subtype.mk_eq_mk] at h
  obtain ⟨e⟩ := linearEquiv_of_isotypicComponent_eq h
  exact eq_of_asModule_linearEquiv e

noncomputable instance [Finite G] : Fintype (UnitaryDual ℂ G) := .ofFinite _

lemma ofUnitaryRepresentation_apply_eq_one_iff {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] [FiniteDimensional 𝕜 E]
    (ρ : UnitaryRepresentation 𝕜 G E) (hρ : ρ.toRepresentation.IsIrreducible) {x : G} :
    (ofUnitaryRepresentation ρ hρ).ρ x = 1 ↔ ρ x = 1 :=
  have : (ofUnitaryRepresentation ρ hρ).out.1 ≅ UnitaryRep.of ρ :=
    (ObjectProperty.ι _).mapIso <| fromSkeletonToSkeletonIso
      (⟨UnitaryRep.of ρ, hρ⟩ : ObjectProperty.FullSubcategory
        fun ψ : UnitaryRep 𝕜 G ↦ ψ.ρ.toRepresentation.IsIrreducible)
  ⟨fun h ↦ UnitaryRep.map_eq_one_of_iso this h,
    fun h ↦ UnitaryRep.map_eq_one_of_iso this.symm h⟩

lemma finrank_real_continuousLinearMap (ψ : UnitaryDual ℂ G) :
    finrank ℝ (ψ.E →L[ℂ] ψ.E) = 2 * finrank ℂ ψ.E ^ 2 := by
  rw [← finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    ← LinearMap.toContinuousLinearMap.finrank_eq, finrank_linearMap, sq]

lemma exists_apply_ne_one [Finite G] {x : G} (hx : x ≠ 1) :
    ∃ ψ : UnitaryDual ℂ G, ψ.ρ x ≠ 1 := by
  classical
  cases nonempty_fintype G
  by_contra! h
  have h_irred (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      [FiniteDimensional ℂ V] (σ : UnitaryRepresentation ℂ G V)
      (hσ : σ.toRepresentation.IsIrreducible) : σ x = 1 :=
    (ofUnitaryRepresentation_apply_eq_one_iff σ hσ).mp (h (ofUnitaryRepresentation σ hσ))
  exact regular_apply_ne_one hx (congr_eq_one_iff.mp
    (apply_eq_one_of_forall_isIrreducible x h_irred _
      ((regular ℂ G).congr (.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFin G)))))

end Group

section CommGroup
variable [CommGroup G] {ψ : UnitaryDual ℂ G}

variable (ψ) in
@[simp] lemma finrank_E_eq_one : Module.finrank ℂ ψ.E = 1 :=
  UnitaryRepresentation.finrank_eq_one_of_isIrreducible isIrreducible_ρ

end CommGroup
end UnitaryDual
