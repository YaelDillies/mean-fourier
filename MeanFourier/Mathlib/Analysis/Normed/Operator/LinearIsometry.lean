module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry

public section

variable {𝓕 R R₂ E E₂ : Type*} [Semiring R] [Semiring R₂] {σ₁₂ : R →+* R₂}
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂] [Module R E] [Module R₂ E₂]
  [FunLike 𝓕 E E₂]

instance [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] : IsometryClass 𝓕 E E₂ where
  isometry := SemilinearIsometryClass.isometry

namespace LinearIsometryEquiv

attribute [coe] toContinuousLinearEquiv

@[simp] lemma toContinuousLinearEquiv_one : toContinuousLinearEquiv (1 : E ≃ₗᵢ[R] E) = 1 := rfl

@[simp] lemma toContinuousLinearEquiv_mul (e e' : E ≃ₗᵢ[R] E) :
    toContinuousLinearEquiv (e * e') = e.toContinuousLinearEquiv * e'.toContinuousLinearEquiv := rfl

@[simp] lemma toContinuousLinearEquiv_inv (e : E ≃ₗᵢ[R] E) :
    toContinuousLinearEquiv e⁻¹ = e.toContinuousLinearEquiv⁻¹ := rfl

end LinearIsometryEquiv
