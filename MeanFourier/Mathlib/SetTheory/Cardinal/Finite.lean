module

public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace ENat
variable {α : Type*} [Nonempty α]

@[simp] lemma card_ne_zero : card α ≠ 0 := (card_ne_zero_iff_nonempty _).2 ‹_›

end ENat
