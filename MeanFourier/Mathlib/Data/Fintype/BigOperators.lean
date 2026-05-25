module

public import Mathlib.Data.Fintype.BigOperators
public import MeanFourier.Mathlib.Data.Finset.Pi

public section

namespace Finset
variable {ι : Type*} {α : ι → Type*} {s : Finset ι} {t : ∀ i, Finset (α i)}

lemma card_pi' (ht : ∀ i ∉ s, ∃ x, t i = {x}) :
    #(s.pi' t fun i hi ↦ by obtain ⟨x, hx⟩ := ht i hi; simp [hx]) = ∏ i ∈ s, #(t i) := by
  classical choose x hx using id ht; rw [pi'_of_forall_singleton x hx, card_map, card_pi]

end Finset
