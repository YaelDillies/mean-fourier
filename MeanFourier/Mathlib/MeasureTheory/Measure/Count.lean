module

public import Mathlib.MeasureTheory.Measure.Count
public import MeanFourier.Mathlib.Data.Real.ENatENNReal
public import MeanFourier.Mathlib.SetTheory.Cardinal.Finite

import Mathlib.SetTheory.Cardinal.NatCard

public section

namespace ENNReal

@[simp]
lemma toReal_enatCard (α : Type*) [Finite α] : ENNReal.toReal (ENat.card α) = Nat.card α := by
  simp [ENat.card_eq_coe_natCard]

end ENNReal

namespace MeasureTheory.Measure
variable {α : Type*} [MeasurableSpace α]

instance neZero_count [Nonempty α] : NeZero (count : Measure α) where
  out := by rintro h; simpa using congr($h .univ)

@[simp] lemma count_real_univ [Finite α] : count.real (.univ : Set α) = Nat.card α := by
  simp [Measure.real]

end MeasureTheory.Measure
