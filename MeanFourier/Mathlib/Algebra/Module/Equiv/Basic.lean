module

public import Mathlib.Algebra.Module.Equiv.Basic

public section

namespace LinearEquiv
variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

-- TODO: Replace `coe_toLinearMap_one`
@[simp high] lemma toLinearMap_one : toLinearMap (1 : M ≃ₗ[R] M) = 1 := rfl

end LinearEquiv
