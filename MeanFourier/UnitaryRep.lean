/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import MeanFourier.UnitaryRepresentation

/-!
# The category of unitary representations of a group

For `𝕜 = ℝ, ℂ`, this file defines the category of `𝕜`-valued unitary representations
-/

public noncomputable section

universe u

open CategoryTheory

variable {ι 𝕜 G : Type*} {E F H : Type u} [RCLike 𝕜]

variable (𝕜 G) [Group G] in
/-- The category of unitary representations of a group `G` and their morphisms. -/
structure UnitaryRep where
  /-- Construct an object in `UnitaryRep 𝕜 G` from its underlying unitary representation. -/
  of ::
  /-- The underlying finite-dimensional Hilbert space of an object in `UnitaryRep 𝕜 G` -/
  {E : Type u}
  [normedAddCommGroup : NormedAddCommGroup E]
  [innerProductSpace : InnerProductSpace 𝕜 E]
  [completeSpace : CompleteSpace E]
  /-- The underlying unitary representation of an object in `UnitaryRep 𝕜 G` -/
  ρ : UnitaryRepresentation 𝕜 G E

namespace UnitaryRep

attribute [instance] normedAddCommGroup innerProductSpace completeSpace

initialize_simps_projections UnitaryRep
  (-normedAddCommGroup, -innerProductSpace, -completeSpace)

section Group
variable [Group G]

instance : CoeSort (UnitaryRep.{u} 𝕜 G) (Type u) where coe := UnitaryRep.E

variable {A B C : UnitaryRep.{u} 𝕜 G}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {ρ : UnitaryRepresentation 𝕜 G E} {σ : UnitaryRepresentation 𝕜 G F}
  {τ : UnitaryRepresentation 𝕜 G H}

variable (A B) in
/-- The type of morphisms in `UnitaryRep.{u} 𝕜 G`. -/
@[ext]
structure Hom where
  private mk ::
  /-- The underlying `G`-equivariant linear map. -/
  hom' : A.ρ.toRepresentation.IntertwiningMap B.ρ.toRepresentation

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category (UnitaryRep.{u} 𝕜 G) where
  Hom A B := Hom A B
  id A := ⟨1⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance :
    ConcreteCategory (UnitaryRep.{u} 𝕜 G) fun A B ↦
      A.ρ.toRepresentation.IntertwiningMap B.ρ.toRepresentation where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `UnitaryRep` back into an `IntertwiningMap`. -/
abbrev Hom.hom (f : Hom A B) := ConcreteCategory.hom (C := UnitaryRep 𝕜 G) f

/-- Typecheck an `IntertwiningMap` as a morphism in `UnitaryRep`. -/
abbrev ofHom (f : ρ.toRepresentation.IntertwiningMap σ.toRepresentation) : of ρ ⟶ of σ :=
  ConcreteCategory.ofHom (C := UnitaryRep.{u} 𝕜 G) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = 1 := rfl

/- Provided for rewriting. -/
lemma id_apply (a : A) : (𝟙 A : A ⟶ A) a = a := by simp

@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf

lemma hom_comm_apply (f : A ⟶ B) (g : G) (a : A) : f.hom (A.ρ g a) = B.ρ g (f.hom a) := by
  simpa using congr($(f.hom.2 g) a)

@[simp] lemma hom_ofHom (f : ρ.toRepresentation.IntertwiningMap σ.toRepresentation) :
    (ofHom f).hom = f := rfl

@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom f.hom = f := rfl

@[simp] lemma ofHom_id : ofHom (.id ρ.toRepresentation) = 𝟙 (of ρ) := rfl

@[simp]
lemma ofHom_comp (f : ρ.toRepresentation.IntertwiningMap σ.toRepresentation)
    (g : σ.toRepresentation.IntertwiningMap τ.toRepresentation) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

lemma ofHom_apply (f : ρ.toRepresentation.IntertwiningMap σ.toRepresentation) (x : E) :
    ofHom f x = f x := rfl

lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv.hom (e.hom.hom x) = x := by simp
lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom.hom (e.inv.hom x) = x := by simp

lemma forget_obj : (forget (UnitaryRep.{u} 𝕜 G)).obj A = A := rfl

lemma forget_map (f : A ⟶ B) : (forget (UnitaryRep.{u} 𝕜 G)).map f = (f : _ → _) := rfl

/-- An equiv between the underlying representations induce isomorphism between objects in
`UnitaryRep 𝕜 G`. -/
@[expose]
def mkIso (e : ρ.toRepresentation.Equiv σ.toRepresentation) : of ρ ≅ of σ where
  hom := ofHom e.toIntertwiningMap
  inv := ofHom e.symm.toIntertwiningMap

@[simp]
lemma mkIso_hom_hom_apply (e : ρ.toRepresentation.Equiv σ.toRepresentation) (x : E) :
    (mkIso e).hom.hom x = e.toLinearMap x := rfl

@[simp]
lemma mkIso_hom_hom_toLinearMap (e : ρ.toRepresentation.Equiv σ.toRepresentation) :
    (mkIso e).hom.hom.toLinearMap = e.toLinearMap := rfl

@[simp]
lemma mkIso_inv_hom_toLinearMap (e : ρ.toRepresentation.Equiv σ.toRepresentation) :
    (mkIso e).inv.hom.toLinearMap = e.symm.toIntertwiningMap.toLinearMap := rfl

@[simp]
lemma mkIso_inv_hom_apply (e : ρ.toRepresentation.Equiv σ.toRepresentation) (y : F) :
    (mkIso e).inv.hom y = e.symm y := rfl

@[simp]
lemma mkIso_hom_hom (e : ρ.toRepresentation.Equiv σ.toRepresentation) :
    (mkIso e).hom.hom = e.toIntertwiningMap := rfl

/-- The equivalence between representations induced from iso between objects in `UnitaryRep 𝕜 G`. -/
@[expose, simps]
def equivOfIso (i : A ≅ B) : A.ρ.toRepresentation.Equiv B.ρ.toRepresentation where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

instance reflectsIsomorphisms_forget : (forget (UnitaryRep.{u} 𝕜 G)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (UnitaryRep.{u} 𝕜 G)).map f)
    let e : X.ρ.toRepresentation.Equiv Y.ρ.toRepresentation := { f.hom, i.toEquiv with }
    exact (mkIso e).isIso_hom

lemma hom_bijective :
    (Hom.hom : (A ⟶ B) → A.ρ.toRepresentation.IntertwiningMap B.ρ.toRepresentation).Bijective where
  left _ _ h := UnitaryRep.hom_ext h
  right f := ⟨ofHom f, hom_ofHom f⟩

/-- Convenience shortcut for `UnitaryRep.hom_bijective.injective`. -/
lemma hom_injective :
    (Hom.hom : (A ⟶ B) → A.ρ.toRepresentation.IntertwiningMap B.ρ.toRepresentation).Injective :=
  hom_bijective.injective

/-- Convenience shortcut for `UnitaryRep.hom_bijective.surjective`. -/
lemma hom_surjective :
    (Hom.hom : (A ⟶ B) → A.ρ.toRepresentation.IntertwiningMap B.ρ.toRepresentation).Surjective :=
  hom_bijective.surjective

/-- The morphisms between two objects in `UnitaryRep 𝕜 G` are equivalent to the intertwining maps
between their underlying representations. -/
@[expose, simps]
def homEquiv : (A ⟶ B) ≃ A.ρ.toRepresentation.IntertwiningMap B.ρ.toRepresentation where
  toFun := Hom.hom
  invFun := ofHom

instance : Add (A ⟶ B) where add f g := ofHom (f.hom + g.hom)

lemma ofHom_add (f g : ρ.toRepresentation.IntertwiningMap σ.toRepresentation) :
    ofHom (f + g) = ofHom f + ofHom g := rfl

lemma add_hom (f g : A ⟶ B) : (f + g).hom = f.hom + g.hom := rfl

lemma hom_comp_toLinearMap (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom.toLinearMap = g.hom.toLinearMap ∘ₗ f.hom.toLinearMap := rfl

lemma add_comp (f₁ f₂ : A ⟶ B) (g : B ⟶ C) :
    (f₁ + f₂) ≫ g = f₁ ≫ g + f₂ ≫ g := by
  ext1
  simp [add_hom, Representation.IntertwiningMap.add_comp]

lemma comp_add (f : A ⟶ B) (g₁ g₂ : B ⟶ C) :
    f ≫ (g₁ + g₂) = f ≫ g₁ + f ≫ g₂ := by
  ext1
  simp [add_hom, Representation.IntertwiningMap.comp_add]

instance : Zero (A ⟶ B) where
  zero := ofHom (0 : A.ρ.toRepresentation.IntertwiningMap B.ρ.toRepresentation)

@[simp]
lemma ofHom_zero : ofHom (0 : ρ.toRepresentation.IntertwiningMap σ.toRepresentation) = 0 := rfl

@[simp]
lemma zero_hom : (0 : A ⟶ B).hom = 0 := rfl

instance : SMul ℕ (A ⟶ B) where smul n f := ofHom (n • f.hom)

lemma ofHom_nsmul (f : ρ.toRepresentation.IntertwiningMap σ.toRepresentation) (n : ℕ) :
    ofHom (n • f) = n • ofHom f := rfl

lemma nsmul_hom (f : A ⟶ B) (n : ℕ) : (n • f).hom = n • f.hom := rfl

instance : Neg (A ⟶ B) where neg f := ofHom (-f.hom)

lemma ofHom_neg (f : ρ.toRepresentation.IntertwiningMap σ.toRepresentation) :
    ofHom (-f) = -ofHom f := rfl

lemma neg_hom (f : A ⟶ B) : (-f).hom = -f.hom := rfl

instance : Sub (A ⟶ B) where sub f g := ofHom (f.hom - g.hom)

lemma ofHom_sub (f g : ρ.toRepresentation.IntertwiningMap σ.toRepresentation) :
    ofHom (f - g) = ofHom f - ofHom g := rfl

lemma sub_hom (f g : A ⟶ B) : (f - g).hom = f.hom - g.hom := rfl

instance : SMul ℤ (A ⟶ B) where smul n f := ofHom (n • f.hom)

lemma ofHom_zsmul (f : ρ.toRepresentation.IntertwiningMap σ.toRepresentation) (n : ℤ) :
    ofHom (n • f) = n • ofHom f := rfl

lemma zsmul_hom (f : A ⟶ B) (n : ℤ) : (n • f).hom = n • f.hom := rfl

instance : AddCommGroup (A ⟶ B) := fast_instance% hom_injective.addCommGroup
    UnitaryRep.Hom.hom zero_hom add_hom neg_hom sub_hom nsmul_hom zsmul_hom

instance : Preadditive (UnitaryRep.{u} 𝕜 G) where
  add_comp _ _ _ := add_comp
  comp_add _ _ _ := comp_add

lemma sum_hom (f : ι → (A ⟶ B)) (s : Finset ι) : (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom := by
  classical induction s using Finset.induction with
  | empty => simp
  | insert a s ha h => simp [Finset.sum_insert ha, add_hom, h]

lemma ofHom_sum (f : ι → σ.toRepresentation.IntertwiningMap ρ.toRepresentation) (s : Finset ι) :
    ofHom (∑ i ∈ s, f i) = ∑ i ∈ s, ofHom (f i) := by
  induction s using Finset.cons_induction <;> simp [ofHom_add, *]

variable (𝕜 G E) in
/-- The trivial `𝕜`-linear `G`-representation on a `𝕜`-module `V.` -/
@[simps -isSimp]
abbrev trivial : UnitaryRep 𝕜 G := of (.trivial 𝕜 G E)

@[simp]
lemma trivial_ρ_apply (g : G) (x : E) : (trivial 𝕜 G E).ρ g x = x := rfl

instance : Inhabited (UnitaryRep 𝕜 G) where default := .trivial 𝕜 G PUnit

lemma ρ_mul (g1 g2 : G) : A.ρ (g1 * g2) = (A.ρ g2).trans (A.ρ g1) := by ext; simp

end Group
end UnitaryRep
