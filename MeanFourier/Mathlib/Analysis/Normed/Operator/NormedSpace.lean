module

public import Mathlib.Analysis.Normed.Operator.NormedSpace

public section

namespace ContinuousLinearMap
variable {𝕜₁ 𝕜₂ 𝕜₃ E F G : Type*}
  [NontriviallyNormedField 𝕜₁] [NormedAddCommGroup E] [NormedSpace 𝕜₁ E]
  [NontriviallyNormedField 𝕜₂] [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]
  [NontriviallyNormedField 𝕜₃] [NormedAddCommGroup G] [NormedSpace 𝕜₃ G]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₃₂ : 𝕜₃ →+* 𝕜₂} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
  {σ₁₃ : 𝕜₁ →+* 𝕜₃} [RingHomIsometric σ₁₃]
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/-- Postcomposition with a linear isometry preserves the operator norm. -/
@[simp]
lemma opNNNorm_comp_linearIsometryEquiv [RingHomIsometric σ₂₃] (f : F →SL[σ₂₃] G)
    (e : E ≃ₛₗᵢ[σ₁₂] F) : ‖f.comp (e : E →SL[σ₁₂] F)‖₊ = ‖f‖₊ :=
  eq_of_forall_ge_iff fun r ↦ by simp [opNNNorm_le_iff, ← e.forall_congr_right]

/-- Postcomposition with a linear isometry preserves the operator norm. -/
@[simp]
lemma opNNNorm_linearIsometryEquiv_comp [RingHomIsometric σ₁₂] (e : F ≃ₛₗᵢ[σ₂₃] G)
    (f : E →SL[σ₁₂] F) : ‖(e : F →SL[σ₂₃] G).comp f‖₊ = ‖f‖₊ :=
  eq_of_forall_ge_iff fun r ↦ by simp [opNNNorm_le_iff]

/-- Postcomposition with a linear isometry preserves the operator norm. -/
@[simp]
lemma opNorm_comp_linearIsometryEquiv' [RingHomIsometric σ₂₃] (f : F →SL[σ₂₃] G)
    (e : E ≃ₛₗᵢ[σ₁₂] F) : ‖f.comp (e : E →SL[σ₁₂] F)‖ = ‖f‖ :=
  congr($(opNNNorm_comp_linearIsometryEquiv f e))

/-- Postcomposition with a linear isometry preserves the operator norm. -/
@[simp]
lemma opNorm_linearIsometryEquiv_comp [RingHomIsometric σ₁₂] (e : F ≃ₛₗᵢ[σ₂₃] G)
    (f : E →SL[σ₁₂] F) : ‖(e : F →SL[σ₂₃] G).comp f‖ = ‖f‖ :=
  congr($(opNNNorm_linearIsometryEquiv_comp e f))

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Postcomposition with a linear isometry preserves the operator norm. -/
@[simp]
lemma opNNNorm_mul_linearIsometryEquiv (f : E →L[𝕜] E) (e : E ≃ₗᵢ[𝕜] E) : ‖f * e‖₊ = ‖f‖₊ :=
  opNNNorm_comp_linearIsometryEquiv ..

/-- Postcomposition with a linear isometry preserves the operator norm. -/
@[simp]
lemma opNNNorm_linearIsometryEquiv_mul (e : E ≃ₗᵢ[𝕜] E) (f : E →L[𝕜] E) : ‖e * f‖₊ = ‖f‖₊ :=
  opNNNorm_linearIsometryEquiv_comp ..

/-- Postcomposition with a linear isometry preserves the operator norm. -/
@[simp]
lemma opNorm_mul_linearIsometryEquiv (f : E →L[𝕜] E) (e : E ≃ₗᵢ[𝕜] E) : ‖f * e‖ = ‖f‖ :=
  opNorm_comp_linearIsometryEquiv' ..

/-- Postcomposition with a linear isometry preserves the operator norm. -/
@[simp]
lemma opNorm_linearIsometryEquiv_mul (e : E ≃ₗᵢ[𝕜] E) (f : E →L[𝕜] E) : ‖e * f‖ = ‖f‖ :=
  opNorm_linearIsometryEquiv_comp ..

end ContinuousLinearMap
