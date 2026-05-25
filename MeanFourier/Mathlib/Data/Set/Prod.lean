module

public import Mathlib.Data.Set.Prod

public section

attribute [congr] Set.pi_congr

namespace Set
variable {ι : Type*} {α : ι → Type*} {s : Set ι} {t : ∀ i, Set (α i)}

lemma pi_nonempty : (s.pi t).Nonempty ↔ (∀ i, Nonempty (α i)) ∧ ∀ i ∈ s, (t i).Nonempty := by
  rw [pi_nonempty_iff, ← forall_and]
  congr! with i
  by_cases hi : i ∈ s
  · simpa [hi, ← Set.Nonempty.eq_def] using Set.Nonempty.to_type
  · simp [hi]

end Set
