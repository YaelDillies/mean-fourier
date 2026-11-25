module

public import Mathlib.Algebra.Star.Pi

public section

open scoped ComplexConjugate

namespace Pi

/-- Unapplied form of `Pi.conj_apply`, tagged `push ←` so that `@[to_fun]` can eta-expand `conj f`
into `fun i ↦ conj (f i)`. -/
@[push ←]
lemma conj_def {ι : Type*} {α : ι → Type*} [∀ i, CommSemiring (α i)] [∀ i, StarRing (α i)]
    (f : ∀ i, α i) : conj f = fun i ↦ conj (f i) := rfl

end Pi
