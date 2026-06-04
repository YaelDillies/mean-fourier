module

public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import MeanFourier.Mathlib.Data.ENat.BigOperators
public import MeanFourier.Mathlib.Data.Set.Prod
public import MeanFourier.Mathlib.Topology.MetricSpace.Cover
public import MeanFourier.Mathlib.Topology.MetricSpace.MetricSeparated

open scoped NNReal ENNReal

public section

namespace Metric
variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {f : X → Y} {s C P : Set X}
  {t C' : Set Y} {K ε : ℝ≥0} {n : ℕ∞}

lemma le_coveringNumber_iff : n ≤ coveringNumber ε s ↔ ∀ C ⊆ s, IsCover ε s C → n ≤ C.encard := by
  simp [coveringNumber]

lemma packingNumber_le_iff : packingNumber ε s ≤ n ↔ ∀ P ⊆ s, IsSeparated ε P → P.encard ≤ n := by
  simp [packingNumber]

@[simp] lemma one_le_coveringNumber_iff : 1 ≤ coveringNumber ε s ↔ s.Nonempty := by
  simp [Order.one_le_iff_ne_zero, Set.nonempty_iff_ne_empty]

lemma coveringNumber_ne_zero_iff : coveringNumber ε s ≠ 0 ↔ s.Nonempty := by
  simp [Set.nonempty_iff_ne_empty]

@[simp] lemma one_le_externalCoveringNumber_iff : 1 ≤ externalCoveringNumber ε s ↔ s.Nonempty := by
  simp [Order.one_le_iff_ne_zero, Set.nonempty_iff_ne_empty]

lemma externalCoveringNumber_ne_zero_iff : externalCoveringNumber ε s ≠ 0 ↔ s.Nonempty := by
  simp [Set.nonempty_iff_ne_empty]

@[simp] lemma one_le_packingNumber_iff : 1 ≤ packingNumber ε s ↔ s.Nonempty := by
  simp [Order.one_le_iff_ne_zero, Set.nonempty_iff_ne_empty]

lemma packingNumber_ne_zero_iff : packingNumber ε s ≠ 0 ↔ s.Nonempty := by
  simp [Set.nonempty_iff_ne_empty]

@[simp] alias ⟨_, coveringNumber_pos⟩ := coveringNumber_pos_iff
@[simp] alias ⟨_, coveringNumber_ne_zero⟩ := coveringNumber_ne_zero_iff
@[simp] alias ⟨_, one_le_coveringNumber⟩ := one_le_coveringNumber_iff

@[simp] alias ⟨_, externalCoveringNumber_pos⟩ := externalCoveringNumber_pos_iff
@[simp] alias ⟨_, externalCoveringNumber_ne_zero⟩ := externalCoveringNumber_ne_zero_iff
@[simp] alias ⟨_, one_le_externalCoveringNumber⟩ := one_le_externalCoveringNumber_iff

@[simp] alias ⟨_, packingNumber_pos⟩ := packingNumber_pos_iff
@[simp] alias ⟨_, packingNumber_ne_zero⟩ := packingNumber_ne_zero_iff
@[simp] alias ⟨_, one_le_packingNumber⟩ := one_le_packingNumber_iff

lemma packingNumber_two_mul_le_coveringNumber : packingNumber (2 * ε) s ≤ coveringNumber ε s := by
  grw [packingNumber_two_mul_le_externalCoveringNumber, externalCoveringNumber_le_coveringNumber]

/-- The smallness of the packing number is quantitatively pulled back under antilipschitz maps. -/
lemma packingNumber_le_packingNumber_of_antilipschitzWith (hst : s.MapsTo f t)
    (hf : AntilipschitzWith K f) : packingNumber (K * ε) s ≤ packingNumber ε t := by
  refine packingNumber_le_iff.2 fun P hPs hP ↦ ?_
  rw [← (hf.injOn hP).encard_image]
  exact (hP.image_of_antilipschitzWith hf).encard_le_packingNumber (by grw [hPs, hst.image_subset])

/-- The smallness of the covering number is quantitatively pulled back under antilipschitz maps. -/
lemma coveringNumber_le_coveringNumber_of_antilipschitzWith (hst : s.MapsTo f t)
    (hf : AntilipschitzWith K f) : coveringNumber (2 * K * ε) s ≤ coveringNumber ε t := by
  grw [coveringNumber_le_packingNumber, mul_assoc, mul_left_comm,
    packingNumber_le_packingNumber_of_antilipschitzWith hst hf,
    packingNumber_two_mul_le_coveringNumber]

/-- The smallness of the covering number is quantitatively pushed forward under surjective lipschitz
maps. -/
lemma coveringNumber_le_coveringNumber_of_lipschitzOnWith (hst : s.SurjOn f t) (hst' : s.MapsTo f t)
    (hf : LipschitzOnWith K f s) : coveringNumber (K * ε) t ≤ coveringNumber ε s := by
  rw [le_coveringNumber_iff]
  rintro C hCs hC
  grw [← Set.encard_image_le (f := f)]
  exact (hC.image hf hst hCs).coveringNumber_le_encard (by grw [hCs, hst'.image_subset])

/-- The smallness of the covering number is quantitatively pushed forward under surjective lipschitz
maps. -/
lemma packingNumber_le_packingNumber_of_lipschitzOnWith (hst : s.SurjOn f t) (hst' : s.MapsTo f t)
    (hf : LipschitzOnWith K f s) : packingNumber (2 * K * ε) t ≤ packingNumber ε s := by
  grw [mul_assoc, packingNumber_two_mul_le_coveringNumber,
    coveringNumber_le_coveringNumber_of_lipschitzOnWith hst hst' hf,
    coveringNumber_le_packingNumber]

lemma coveringNumber_prod_le :
    coveringNumber ε (s ×ˢ t) ≤ coveringNumber ε s * coveringNumber ε t := by
  obtain rfl | hs₀ := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht₀ := t.eq_empty_or_nonempty
  · simp
  by_cases hs : coveringNumber ε s = ⊤
  · simp [hs, coveringNumber_ne_zero ht₀]
  by_cases ht : coveringNumber ε t = ⊤
  · simp [ht, coveringNumber_ne_zero hs₀]
  rw [← encard_minimalCover hs, ← encard_minimalCover ht, ← Set.encard_prod]
  exact ((isCover_minimalCover hs).prod <| isCover_minimalCover ht).coveringNumber_le_encard
    (by grw [minimalCover_subset, minimalCover_subset])

lemma packingNumber_prod_le :
    packingNumber ε (s ×ˢ t) ≤ packingNumber (ε / 2) s * packingNumber (ε / 2) t := by
  grw [← coveringNumber_le_packingNumber _ s, ← coveringNumber_le_packingNumber _ t,
    ← coveringNumber_prod_le, ← packingNumber_two_mul_le_coveringNumber]
  field_simp
  rfl

-- TODO: Remove the `/ 2` by introducing the external version of `minimalCover`.
lemma externalCoveringNumber_prod_le :
    externalCoveringNumber ε (s ×ˢ t) ≤
      externalCoveringNumber (ε / 2) s * externalCoveringNumber (ε / 2) t := by
  grw [externalCoveringNumber_le_coveringNumber, coveringNumber_prod_le,
    ← coveringNumber_two_mul_le_externalCoveringNumber,
    ← coveringNumber_two_mul_le_externalCoveringNumber]
  field_simp
  rfl

variable {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, PseudoEMetricSpace (X i)]
  {s : ∀ i, Set (X i)}

lemma coveringNumber_pi_univ_le : coveringNumber ε (.pi .univ s) ≤ ∏ i, coveringNumber ε (s i) := by
  classical
  obtain hs₀ | hs₀ := (Set.univ.pi s).eq_empty_or_nonempty
  · simp [hs₀]
  simp [Set.univ_pi_nonempty_iff] at hs₀
  by_cases hs : ∏ i, coveringNumber ε (s i) = ⊤
  · simp [hs]
  simp only [ENat.prod_eq_top, Finset.mem_univ, true_and, ne_eq, coveringNumber_eq_zero,
    (hs₀ _).ne_empty, not_false_eq_true, imp_self, implies_true, and_true, not_exists] at hs
  calc
    coveringNumber ε (Set.univ.pi s)
    _ ≤ (Set.univ.pi fun i ↦ minimalCover ε (s i)).encard :=
      (IsCover.pi fun i _ ↦ isCover_minimalCover <| hs _).coveringNumber_le_encard
        (by gcongr with i; exact minimalCover_subset)
    _ = ∏ i, (minimalCover ε (s i)).encard := by simp
    _ = ∏ i, coveringNumber ε (s i) := by
      congr! 1 with i hi; exact encard_minimalCover (hs i)

lemma packingNumber_pi_univ_le :
    packingNumber ε (.pi .univ s) ≤ ∏ i, packingNumber (ε / 2) (s i) := by
  trans ∏ i, coveringNumber (ε / 2) (s i)
  · grw [← coveringNumber_pi_univ_le, ← packingNumber_two_mul_le_coveringNumber]
    field_simp
    rfl
  · gcongr with i
    exact coveringNumber_le_packingNumber ..

-- TODO: Remove the `/ 2` by introducing the external version of `minimalCover`.
lemma externalCoveringNumber_pi_univ_le :
    externalCoveringNumber ε (.pi .univ s) ≤ ∏ i, externalCoveringNumber (ε / 2) (s i) := by
  grw [externalCoveringNumber_le_coveringNumber, coveringNumber_pi_univ_le]
  gcongr with i
  grw [← coveringNumber_two_mul_le_externalCoveringNumber]
  field_simp
  rfl

end Metric
