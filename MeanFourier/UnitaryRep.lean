/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import MeanFourier.Mathlib.Analysis.InnerProductSpace.Defs
public import MeanFourier.UnitaryRepresentation

/-!
# The category of unitary representations of a group

For `𝕜 = ℝ, ℂ`, this file defines the category of `𝕜`-valued unitary representations
-/

public noncomputable section

universe w w' u u' v v'

open CategoryTheory

variable {ι 𝕜 G : Type*} {E F H : Type w} [RCLike 𝕜]

variable (𝕜 G) [Group G] in
/-- The category of unitary representations of a group `G` and their morphisms. -/
structure UnitaryRep where
  /-- Construct an object in `UnitaryRep 𝕜 G` from its underlying unitary representation. -/
  of ::
  /-- The underlying finite-dimensional Hilbert space of an object in `UnitaryRep 𝕜 G` -/
  {E : Type w}
  [normedAddCommGroup : NormedAddCommGroup E]
  [normedSpace : InnerProductSpace 𝕜 E]
  [finiteDimensional : FiniteDimensional 𝕜 E]
  /-- The underlying unitary representation of an object in `UnitaryRep 𝕜 G` -/
  ρ : Representation 𝕜 G E
  isUnitary_ρ : ρ.IsUnitary

namespace UnitaryRep

attribute [instance] normedAddCommGroup normedSpace finiteDimensional

initialize_simps_projections UnitaryRep (-normedAddCommGroup, -normedSpace, -finiteDimensional)

attribute [coe] E

section Group
variable [Group G]

instance : CoeSort (UnitaryRep 𝕜 G) (Type w) where coe := UnitaryRep.E

variable {A B C : UnitaryRep.{w} 𝕜 G}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {ρ : Representation 𝕜 G E}
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] {σ : Representation 𝕜 G F}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H] {τ : Representation 𝕜 G H}

variable (A B) in
/-- The type of morphisms in `UnitaryRep.{w} 𝕜 G`. -/
@[ext]
structure Hom where
  private mk ::
  /-- The underlying `G`-equivariant linear map. -/
  hom' : A.ρ.IntertwiningMap B.ρ

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category (UnitaryRep.{w} 𝕜 G) where
  Hom A B := Hom A B
  id A := ⟨.id A.ρ⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ConcreteCategory (UnitaryRep.{w} 𝕜 G) (fun A B ↦ A.ρ.IntertwiningMap B.ρ) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `UnitaryRep` back into an `IntertwiningMap`. -/
abbrev Hom.hom (f : Hom A B) := ConcreteCategory.hom (C := UnitaryRep 𝕜 G) f

/-- Typecheck an `IntertwiningMap` as a morphism in `UnitaryRep`. -/
abbrev ofHom (hρ hσ) (f : ρ.IntertwiningMap σ) : of ρ hρ ⟶ of σ hσ :=
  ConcreteCategory.ofHom (C := UnitaryRep.{w} 𝕜 G) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = .id A.ρ := rfl

/- Provided for rewriting. -/
lemma id_apply (a : A) : (𝟙 A : A ⟶ A) a = a := by simp

@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf

lemma hom_comm_apply (f : A ⟶ B) (g : G) (a : A) : f.hom (A.ρ g a) = B.ρ g (f.hom a) := by
  simpa using congr($(f.hom.2 g) a)

@[simp] lemma hom_ofHom (hρ hσ) (f : ρ.IntertwiningMap σ) : (ofHom hρ hσ f).hom = f := rfl
@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom A.isUnitary_ρ B.isUnitary_ρ f.hom = f := rfl

@[simp] lemma ofHom_id (hρ) : ofHom hρ hρ (.id ρ) = 𝟙 (of ρ hρ) := rfl

@[simp]
lemma ofHom_comp (hρ hσ hτ) (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
    ofHom hρ hτ (g.comp f) = ofHom hρ hσ f ≫ ofHom hσ hτ g := rfl

lemma ofHom_apply (hρ hσ) (f : ρ.IntertwiningMap σ) (x : E) : ofHom hρ hσ f x = f x := rfl

lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv.hom (e.hom.hom x) = x := by simp
lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom.hom (e.inv.hom x) = x := by simp

lemma forget_obj : (forget (UnitaryRep.{w} 𝕜 G)).obj A = A := rfl

lemma forget_map (f : A ⟶ B) : (forget (UnitaryRep.{w} 𝕜 G)).map f = (f : _ → _) := rfl

/-- An equiv between the underlying representations induce isomorphism between objects in
`UnitaryRep 𝕜 G`. -/
@[expose]
def mkIso (hρ hσ) (e : ρ.Equiv σ) : of ρ hρ ≅ of σ hσ where
  hom := ofHom hρ hσ e.toIntertwiningMap
  inv := ofHom hσ hρ e.symm.toIntertwiningMap

@[simp]
lemma mkIso_hom_hom_apply (hρ hσ) (e : ρ.Equiv σ) (x : E) :
    (mkIso hρ hσ e).hom.hom x = e.toLinearMap x := rfl

@[simp]
lemma mkIso_hom_hom_toLinearMap (hρ hσ) (e : ρ.Equiv σ) :
    (mkIso hρ hσ e).hom.hom.toLinearMap = e.toLinearMap := rfl

@[simp]
lemma mkIso_inv_hom_toLinearMap (hρ hσ) (e : ρ.Equiv σ) :
    (mkIso hρ hσ e).inv.hom.toLinearMap = e.symm.toIntertwiningMap.toLinearMap := rfl

@[simp]
lemma mkIso_inv_hom_apply (hρ hσ) (e : ρ.Equiv σ) (y : F) :
    (mkIso hρ hσ e).inv.hom y = e.symm y := rfl

@[simp]
lemma mkIso_hom_hom (hρ hσ) (e : ρ.Equiv σ) :
    (mkIso hρ hσ e).hom.hom = e.toIntertwiningMap := rfl

/-- The equivalence between representations induced from iso between objects in `UnitaryRep 𝕜 G`. -/
@[expose, simps]
def equivOfIso (i : A ≅ B) : A.ρ.Equiv B.ρ where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

instance reflectsIsomorphisms_forget : (forget (UnitaryRep.{w} 𝕜 G)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (UnitaryRep.{w} 𝕜 G)).map f)
    let e : X.ρ.Equiv Y.ρ := { f.hom, i.toEquiv with }
    exact (mkIso _ _ e).isIso_hom

lemma hom_bijective :
    Function.Bijective (UnitaryRep.Hom.hom : (A ⟶ B) → (A.ρ.IntertwiningMap B.ρ)) where
  left _ _ h := UnitaryRep.hom_ext h
  right f := ⟨ofHom _ _ f, hom_ofHom _ _ f⟩

/-- Convenience shortcut for `UnitaryRep.hom_bijective.injective`. -/
lemma hom_injective :
    Function.Injective (Hom.hom : (A ⟶ B) → (A.ρ.IntertwiningMap B.ρ)) :=
  hom_bijective.injective

/-- Convenience shortcut for `UnitaryRep.hom_bijective.surjective`. -/
lemma hom_surjective :
    Function.Surjective (Hom.hom : (A ⟶ B) → (A.ρ.IntertwiningMap B.ρ)) :=
  hom_bijective.surjective

/-- The morphisms between two objects in `UnitaryRep 𝕜 G` are equivalent to the intertwining maps
between their underlying representations. -/
@[expose, simps]
def homEquiv : (A ⟶ B) ≃ A.ρ.IntertwiningMap B.ρ where
  toFun := Hom.hom
  invFun := ofHom _ _

instance : Add (A ⟶ B) where add f g := ofHom _ _ (f.hom + g.hom)

lemma ofHom_add (hρ hσ) (f g : ρ.IntertwiningMap σ) :
    ofHom hρ hσ (f + g) = ofHom _ _ f + ofHom _ _ g := rfl

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
  zero := ofHom _ _ (0 : A.ρ.IntertwiningMap B.ρ)

@[simp]
lemma ofHom_zero (hρ hσ) : ofHom hρ hσ (0 : ρ.IntertwiningMap σ) = 0 := rfl

@[simp]
lemma zero_hom : (0 : A ⟶ B).hom = 0 := rfl

instance : SMul ℕ (A ⟶ B) where smul n f := ofHom _ _ (n • f.hom)

lemma ofHom_nsmul (hρ hσ) (f : ρ.IntertwiningMap σ) (n : ℕ) :
    ofHom hρ hσ (n • f) = n • ofHom hρ hσ f := rfl

lemma nsmul_hom (f : A ⟶ B) (n : ℕ) : (n • f).hom = n • f.hom := rfl

instance : Neg (A ⟶ B) where neg f := ofHom _ _ (-f.hom)

lemma ofHom_neg (hρ hσ) (f : ρ.IntertwiningMap σ) : ofHom hρ hσ (-f) = -ofHom _ _ f := rfl

lemma neg_hom (f : A ⟶ B) : (-f).hom = -f.hom := rfl

instance : Sub (A ⟶ B) where sub f g := ofHom _ _ (f.hom - g.hom)

lemma ofHom_sub (hρ hσ) (f g : ρ.IntertwiningMap σ) :
    ofHom hρ hσ (f - g) = ofHom _ _ f - ofHom _ _ g := rfl

lemma sub_hom (f g : A ⟶ B) : (f - g).hom = f.hom - g.hom := rfl

instance : SMul ℤ (A ⟶ B) where smul n f := ofHom _ _ (n • f.hom)

lemma ofHom_zsmul (hρ hσ) (f : ρ.IntertwiningMap σ) (n : ℤ) :
    ofHom hρ hσ (n • f) = n • ofHom _ _ f := rfl

lemma zsmul_hom (f : A ⟶ B) (n : ℤ) : (n • f).hom = n • f.hom := rfl

instance : AddCommGroup (A ⟶ B) := fast_instance% hom_injective.addCommGroup
    UnitaryRep.Hom.hom zero_hom add_hom neg_hom sub_hom nsmul_hom zsmul_hom

instance : Preadditive (UnitaryRep.{w} 𝕜 G) where
  add_comp _ _ _ := add_comp
  comp_add _ _ _ := comp_add

lemma sum_hom {ι : Type u'} (f : ι → (A ⟶ B)) (s : Finset ι) :
    (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom := by
  classical induction s using Finset.induction with
  | empty => simp
  | insert a s ha h => simp [Finset.sum_insert ha, add_hom, h]

lemma ofHom_sum (hρ hσ) (f : ι → σ.IntertwiningMap ρ) (s : Finset ι) :
    ofHom hρ hσ (∑ i ∈ s, f i) = ∑ i ∈ s, ofHom _ _ (f i) := by
  induction s using Finset.cons_induction <;> simp [ofHom_add, *]

variable (𝕜 G E) in
/-- The trivial `𝕜`-linear `G`-representation on a `𝕜`-module `V.` -/
@[simps -isSimp]
abbrev trivial : UnitaryRep 𝕜 G := of (.trivial 𝕜 G E) .trivial

@[simp]
lemma trivial_ρ_apply (g : G) (x : E) : (trivial 𝕜 G E).ρ g x = x := rfl

instance : Inhabited (UnitaryRep.{u} 𝕜 G) where default := .trivial 𝕜 G PUnit

lemma ρ_mul (g1 g2 : G) : A.ρ (g1 * g2) = A.ρ g1 ∘ₗ A.ρ g2 := by ext; simp

end Group
end UnitaryRep
