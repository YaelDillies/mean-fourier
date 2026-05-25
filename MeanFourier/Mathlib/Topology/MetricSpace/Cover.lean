module

public import Mathlib.Topology.MetricSpace.Cover

open scoped NNReal ENNReal

public section

namespace Metric
variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {f : X → Y} {s C P : Set X}
  {t D : Set Y} {K ε : ℝ≥0} {n : ℕ∞}

protected lemma IsCover.prod (hC : IsCover ε s C) (hD : IsCover ε t D) :
    IsCover ε (s ×ˢ t) (C ×ˢ D) := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  obtain ⟨c, hc, hxc⟩ := hC hx
  obtain ⟨d, hd, hyd⟩ := hD hy
  dsimp at *
  exact ⟨(c, d), ⟨hc, hd⟩, by simp [Prod.edist_eq, *]⟩

protected lemma IsCover.pi {ι : Type*} [Fintype ι] {X : ι → Type*} {I : Set ι}
    [∀ i, PseudoEMetricSpace (X i)] {s C : ∀ i, Set (X i)} (hC : ∀ i ∈ I, IsCover ε (s i) (C i)) :
    IsCover ε (I.pi s) (I.pi C) := by
  classical
  rintro x hx
  have (i : ι) : Nonempty (X i) := ⟨x i⟩
  choose! c hc hxc using fun i hi ↦ hC i hi (hx i hi)
  refine ⟨fun i ↦ if i ∈ I then c i else x i, fun i hi ↦ by dsimp; split_ifs; exact hc i hi, ?_⟩
  simp only [edist_pi_def, Finset.sup_le_iff, Finset.mem_univ, forall_const, Set.mem_setOf_eq]
  rintro i
  split_ifs <;> simp_all

end Metric
