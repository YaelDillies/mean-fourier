module

public import Mathlib.Data.ENat.BigOperators

import Mathlib.Algebra.BigOperators.WithTop

public section

namespace ENat
variable {ι : Type*} {s : Finset ι} {f : ι → ℕ∞}

@[simp] lemma prod_eq_top : ∏ i ∈ s, f i = ⊤ ↔ (∃ i ∈ s, f i = ⊤) ∧ ∀ i ∈ s, f i ≠ 0 :=
  WithTop.prod_eq_top_iff

end ENat
