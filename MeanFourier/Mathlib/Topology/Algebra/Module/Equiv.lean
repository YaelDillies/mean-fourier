module

public import Mathlib.Topology.Algebra.Module.Equiv

public section

namespace ContinuousLinearEquiv
variable {R₁ M₁ : Type*} [Semiring R₁] [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R₁ M₁]


@[simp] lemma toContinuousLinearMap_one : toContinuousLinearMap (1 : M₁ ≃L[R₁] M₁) = 1 := rfl

@[simp] lemma toContinuousLinearMap_mul (e e' : M₁ ≃L[R₁] M₁) :
    toContinuousLinearMap (e * e') = e.toContinuousLinearMap * e'.toContinuousLinearMap := rfl


end ContinuousLinearEquiv
