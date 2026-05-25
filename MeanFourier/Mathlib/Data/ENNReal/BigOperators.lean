module

public import Mathlib.Data.ENNReal.BigOperators

public section

namespace ENNReal
variable {ι : Type*} {s : Finset ι} {f : ι → ℝ≥0∞}

@[simp] lemma prod_eq_top : ∏ i ∈ s, f i = ⊤ ↔ (∃ i ∈ s, f i = ⊤) ∧ ∀ i ∈ s, f i ≠ 0 :=
  WithTop.prod_eq_top_iff

end ENNReal
