module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

public section

namespace LinearMap
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

@[simp] lemma id_mem_unitary : LinearMap.id ∈ unitary (E →ₗ[𝕜] E) := one_mem _

end LinearMap
