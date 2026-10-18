module

public import Mathlib.Data.Set.Image

public section

namespace Set
variable {α : Type*}

/-- Inserting a fixed element is injective on the sets avoiding it: the element can be removed
again, recovering the argument. -/
lemma insert_injOn_notMem (a : α) : InjOn (insert a) {s : Set α | a ∉ s} :=
  fun _s hs _t ht h ↦ by rw [← insert_sdiff_self_of_notMem hs, h, insert_sdiff_self_of_notMem ht]

end Set
