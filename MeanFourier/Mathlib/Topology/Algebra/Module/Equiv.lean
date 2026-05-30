module

public import Mathlib.Topology.Algebra.Module.Equiv

public section

namespace ContinuousLinearEquiv
variable {R M : Type*} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]

@[simp] lemma toLinearEquiv_one : toLinearEquiv (1 : M ≃L[R] M) = 1 := rfl

@[simp] lemma toLinearEquiv_mul (e e' : M ≃L[R] M) :
    toLinearEquiv (e * e') = toLinearEquiv e * toLinearEquiv e' := rfl

end ContinuousLinearEquiv
