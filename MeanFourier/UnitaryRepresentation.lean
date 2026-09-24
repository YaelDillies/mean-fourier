/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.RepresentationTheory.Irreducible
public import MeanFourier.Mathlib.Algebra.Module.Equiv.Basic
public import MeanFourier.Mathlib.Topology.Algebra.Module.Equiv

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.RepresentationTheory.Subrepresentation

open Module Submodule

public section

variable {𝕜 G E F : Type*}

section RCLike
variable [RCLike 𝕜] [Group G] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

variable (𝕜 G E) in
abbrev UnitaryRepresentation : Type _ := G →* E ≃ₗᵢ[𝕜] E

namespace UnitaryRepresentation

@[expose, simps]
noncomputable def toRepresentation (ρ : UnitaryRepresentation 𝕜 G E) :
    Representation 𝕜 G E where
  toFun g := ρ g
  map_one' := by simp
  map_mul' := by simp

variable (𝕜 G E) in
abbrev trivial : UnitaryRepresentation 𝕜 G E := 1

variable {ρ : UnitaryRepresentation 𝕜 G E} {W : Submodule 𝕜 E}

@[expose]
def congr (ρ : UnitaryRepresentation 𝕜 G E) (σ : E ≃ₗᵢ[𝕜] F) :
    UnitaryRepresentation 𝕜 G F where
  toFun g := (σ.symm.trans (ρ g)).trans σ
  map_one' := by
    ext
    simp
  map_mul' g h := by
    ext
    simp

@[simp] lemma congr_apply (σ : E ≃ₗᵢ[𝕜] F) (g : G) (v : F) :
    ρ.congr σ g v = σ (ρ g (σ.symm v)) := rfl

@[simp] lemma congr_eq_one_iff {σ : E ≃ₗᵢ[𝕜] F} {g : G} :
    ρ.congr σ g = 1 ↔ ρ g = 1 := by
  simp_rw [LinearIsometryEquiv.ext_iff, congr_apply]
  exact ⟨fun h v ↦ σ.injective
    ((congrArg (σ ∘ ρ g) (σ.symm_apply_apply v)).symm.trans (h (σ v))),
    fun h v ↦ (congrArg σ (h (σ.symm v))).trans (σ.apply_symm_apply v)⟩

lemma inv_apply_apply (g : G) (v : E) : ρ g⁻¹ (ρ g v) = v := by
  simp

lemma apply_inv_apply (g : G) (v : E) : ρ g (ρ g⁻¹ v) = v := by
  simp

lemma map_eq_of_invariant (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) (g : G) :
    W.map ((ρ g).toLinearEquiv : E →ₗ[𝕜] E) = W := by
  refine le_antisymm (map_le_iff_le_comap.2 fun v hv ↦ hW g v hv) fun w hw ↦ ?_
  refine ⟨ρ g⁻¹ w, hW g⁻¹ w hw, ?_⟩
  simp

@[expose]
def restrict (ρ : UnitaryRepresentation 𝕜 G E) (W : Submodule 𝕜 E)
    (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) : UnitaryRepresentation 𝕜 G W where
  toFun g :=
    { (ρ g).toLinearEquiv.ofSubmodules W W (map_eq_of_invariant hW g) with
      norm_map' := fun w ↦ (congrArg norm ((ρ g).toLinearEquiv.ofSubmodules_apply
        (map_eq_of_invariant hW g) w)).trans ((ρ g).norm_map w) }
  map_one' := by
    ext
    simp
  map_mul' g h := by
    ext
    simp

@[simp] lemma coe_restrict_apply (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) (g : G) (w : W) :
    (ρ.restrict W hW g w : E) = ρ g w :=
  (ρ g).toLinearEquiv.ofSubmodules_apply (map_eq_of_invariant hW g) w

lemma invariant_orthogonal (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) (g : G) :
    ∀ v ∈ Wᗮ, ρ g v ∈ Wᗮ := fun v hv w hw ↦ by
  rw [← (ρ g⁻¹).inner_map_map, inv_apply_apply]
  exact hv _ (hW g⁻¹ w hw)

end UnitaryRepresentation
end RCLike

section Induction
universe u
variable [RCLike 𝕜] [Group G]

namespace UnitaryRepresentation

lemma apply_eq_one_of_forall_isIrreducible (x : G)
    (h : ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
      [FiniteDimensional 𝕜 V] (σ : UnitaryRepresentation 𝕜 G V),
      σ.toRepresentation.IsIrreducible → σ x = 1)
    (V : Type u) [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    (ρ : UnitaryRepresentation 𝕜 G V) : ρ x = 1 := by
  suffices ∀ (n : ℕ) (V : Type u) [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
      [FiniteDimensional 𝕜 V] (ρ : UnitaryRepresentation 𝕜 G V),
      finrank 𝕜 V = n → ρ x = 1 from this _ V ρ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
  intro V _ _ _ ρ hn
  cases subsingleton_or_nontrivial V
  · ext v
    exact Subsingleton.elim _ _
  · by_cases hρ : ρ.toRepresentation.IsIrreducible
    · exact h V ρ hρ
    · have : Nontrivial (Subrepresentation ρ.toRepresentation) :=
        ⟨⊥, ⊤, fun heq ↦ bot_ne_top (congrArg Subrepresentation.toSubmodule heq)⟩
      obtain ⟨W, hW_bot, hW_top⟩ :
          ∃ W : Subrepresentation ρ.toRepresentation, W ≠ ⊥ ∧ W ≠ ⊤ := by
        by_contra! h
        exact hρ (IsSimpleOrder.of_forall_eq_top h)
      have hW (g : G) (v : V) (hv : v ∈ W.toSubmodule) : ρ g v ∈ W.toSubmodule :=
        W.apply_mem_toSubmodule g hv
      have : W.toSubmodule ≠ ⊤ :=
        fun heq ↦ hW_top (Subrepresentation.toSubmodule_injective heq)
      have h₁ : ρ.restrict W.toSubmodule hW x = 1 :=
        ih _ (hn ▸ finrank_lt this) _ _ rfl
      have : W.toSubmodule ≠ ⊥ :=
        fun heq ↦ hW_bot (Subrepresentation.toSubmodule_injective heq)
      have h₂ : ρ.restrict W.toSubmoduleᗮ (invariant_orthogonal hW) x = 1 :=
        ih _ (hn ▸ finrank_lt (mt (orthogonal_eq_top_iff (K := W.toSubmodule)).mp this)) _ _ rfl
      ext v
      obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ :
          ∃ w₁ ∈ W.toSubmodule, ∃ w₂ ∈ W.toSubmoduleᗮ, w₁ + w₂ = v := by
        rw [← mem_sup, sup_orthogonal_of_hasOrthogonalProjection]
        exact mem_top
      rw [map_add, ← coe_restrict_apply hW x ⟨w₁, hw₁⟩,
        ← coe_restrict_apply (invariant_orthogonal hW) x ⟨w₂, hw₂⟩, h₁, h₂]
      rfl

end UnitaryRepresentation
end Induction

section Regular
variable [RCLike 𝕜] [Group G]

namespace UnitaryRepresentation
variable (𝕜 G) [Fintype G]

@[expose]
noncomputable def regular : UnitaryRepresentation 𝕜 G (EuclideanSpace 𝕜 G) where
  toFun g := .piLpCongrLeft 2 𝕜 𝕜 (Equiv.mulLeft g)
  map_one' := by
    ext
    simp [Equiv.Perm.one_def, Equiv.piCongrLeft']
  map_mul' g₁ g₂ := by
    ext
    simp [Equiv.Perm.mul_def, Equiv.piCongrLeft']

variable {𝕜 G} in
@[simp] lemma regular_apply_eq_one_iff {x : G} : regular 𝕜 G x = 1 ↔ x = 1 := by
  constructor
  · intro h
    classical
    by_contra hx
    have := congr($h (EuclideanSpace.single 1 1) x)
    simp [regular, hx] at this
  · rintro rfl
    rw [map_one]

variable {𝕜 G} in
lemma regular_apply_ne_one {x : G} (hx : x ≠ 1) : regular 𝕜 G x ≠ 1 :=
  regular_apply_eq_one_iff.not.mpr hx

end UnitaryRepresentation
end Regular

section Complex
variable [CommGroup G] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {ρ : UnitaryRepresentation ℂ G E}

namespace UnitaryRepresentation

lemma finrank_eq_one_of_isIrreducible (hρ : ρ.toRepresentation.IsIrreducible) :
    finrank ℂ E = 1 :=
  hρ.finrank_eq_one_of_isMulCommutative

end UnitaryRepresentation
end Complex
