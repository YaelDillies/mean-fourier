module

public import Mathlib.MeasureTheory.Group.FoelnerFilter

import Mathlib.MeasureTheory.Measure.Real

public section

open MeasureTheory

namespace IsFoelner
variable {G X ι : Type*} [MeasurableSpace X] [Group G] [MulAction G X]
  {μ : Measure X} {l : Filter ι} {u : Ultrafilter ι} {F : ι → Set X}

lemma eventually_measureReal_ne_zero (hF : IsFoelner G μ l F) : ∀ᶠ i in l, μ.real (F i) ≠ 0 := by
  filter_upwards [hF.eventually_meas_ne_zero, hF.eventually_meas_ne_top] with i hi₀ hi
  rwa [measureReal_ne_zero_iff hi]

end IsFoelner
