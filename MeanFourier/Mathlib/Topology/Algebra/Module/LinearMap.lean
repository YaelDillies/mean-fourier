module


public import Mathlib.Topology.Algebra.Module.LinearMap

public section

namespace ContinuousLinearMap
variable {R₁ M₁ : Type*} [Semiring R₁] [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R₁ M₁]

@[simp] lemma mk_one : mk (1 : M₁ →ₗ[R₁] M₁) continuous_id = 1 := rfl

end ContinuousLinearMap
