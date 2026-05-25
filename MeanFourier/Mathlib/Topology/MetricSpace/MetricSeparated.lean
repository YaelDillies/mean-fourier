module

public import Mathlib.Topology.MetricSpace.MetricSeparated

open scoped NNReal ENNReal

public section

namespace Metric
variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {f : X → Y} {s C P : Set X}
  {t C' : Set Y} {K ε : ℝ≥0} {n : ℕ∞}

-- TODO: replace
protected alias IsSeparated.zero := isSeparated_zero

lemma _root_.AntilipschitzWith.injOn (hf : AntilipschitzWith K f) (hs : IsSeparated ε s) :
    s.InjOn f := fun x hx y hy hxy ↦ hs.eq hx hy <| by grw [hf _]; simp [hxy]

lemma IsSeparated.image_of_antilipschitzWith (hf : AntilipschitzWith K f)
    (hs : IsSeparated (K * ε) s) : IsSeparated ε (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
  refine lt_of_mul_lt_mul_left' (a := (K : ℝ≥0∞)) ?_
  grw [← hf _]
  exact hs hx hy (ne_of_apply_ne _ hxy)

end Metric
