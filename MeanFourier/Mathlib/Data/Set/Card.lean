module

public import Mathlib.Data.Set.Card

public section

namespace Set
variable {α β γ : Type*} {f : α → β → γ} {s : Set α} {t : Set β}

lemma ncard_image2_le (hs : s.Finite) (ht : t.Finite) :
    (image2 f s t).ncard ≤ s.ncard * t.ncard := by
  grw [← image_uncurry_prod, ncard_image_le (hs.prod ht), ncard_prod]

end Set
