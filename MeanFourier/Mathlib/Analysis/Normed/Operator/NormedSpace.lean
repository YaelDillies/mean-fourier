module

public import Mathlib.Analysis.Normed.Operator.NormedSpace

public section

-- TODO: Surely `SeminormedAddCommGroup` is enough?

namespace LinearIsometryEquiv
variable {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  [RingHomIsometric σ₁₂] [Nontrivial E]

@[simp] lemma norm_toContinuousLinearMap (e : E ≃ₛₗᵢ[σ₁₂] F) :
    ‖e.toContinuousLinearEquiv.toContinuousLinearMap‖ = 1 :=
  e.toLinearIsometry.norm_toContinuousLinearMap

@[simp] lemma nnnorm_toContinuousLinearMap (e : E ≃ₛₗᵢ[σ₁₂] F) :
    ‖e.toContinuousLinearEquiv.toContinuousLinearMap‖₊ = 1 :=
  e.toLinearIsometry.nnnorm_toContinuousLinearMap

@[simp] lemma enorm_toContinuousLinearMap (e : E ≃ₛₗᵢ[σ₁₂] F) :
    ‖e.toContinuousLinearEquiv.toContinuousLinearMap‖ₑ = 1 :=
  e.toLinearIsometry.enorm_toContinuousLinearMap

end LinearIsometryEquiv
