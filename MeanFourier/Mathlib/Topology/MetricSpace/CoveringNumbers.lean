module

public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import MeanFourier.Mathlib.Data.ENat.BigOperators
public import MeanFourier.Mathlib.Data.Set.Prod
public import MeanFourier.Mathlib.Topology.MetricSpace.Cover
public import MeanFourier.Mathlib.Topology.MetricSpace.MetricSeparated

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

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

-- Nicked from brownian-motion
lemma _root_.TotallyBounded.coveringNumber_ne_top (hs : TotallyBounded s) {r : ℝ≥0} (hr : r ≠ 0) :
    coveringNumber r s ≠ ⊤ := by
  obtain ⟨C, hC_subset, hC_finite, hC_cov⟩ := exists_finite_isCover_of_totallyBounded hr hs
  exact ne_top_of_le_ne_top (by simpa) (hC_cov.coveringNumber_le_encard hC_subset)

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

lemma coveringNumber_le_externalCoveringNumber_half :
    coveringNumber ε s ≤ externalCoveringNumber (ε / 2) s := by
  nth_rw 1 [← mul_div_cancel₀ ε two_ne_zero]
  exact coveringNumber_two_mul_le_externalCoveringNumber (ε / 2) s

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
    exact coveringNumber_le_packingNumber (ε / 2) (s i)

-- TODO: Remove the `/ 2` by introducing the external version of `minimalCover`.
lemma externalCoveringNumber_pi_univ_le :
    externalCoveringNumber ε (.pi .univ s) ≤ ∏ i, externalCoveringNumber (ε / 2) (s i) := by
  trans ∏ i, coveringNumber ε (s i)
  · exact (externalCoveringNumber_le_coveringNumber ε (.pi .univ s)).trans
      coveringNumber_pi_univ_le
  · gcongr with i
    exact coveringNumber_le_externalCoveringNumber_half

lemma div_pow_add_half (R : ℝ) (ε : ℝ) (k : ℕ) :
    (R + ε / 2) ^ k / (ε / 2) ^ k = ((2 * R + ε) / ε) ^ k := by
  rw [← div_pow]
  congr 1
  field_simp

lemma IsSeparated.pairwiseDisjoint_closedBall {α : Type*} [PseudoMetricSpace α] {s : Set α}
    (hsep : IsSeparated ε s) {F : Set α} (hF : F ⊆ s) :
    F.PairwiseDisjoint fun c ↦ closedBall c (ε / 2) := by
  intro a ha b hb hab
  have : (ε : ℝ) < dist a b := by
    simpa [edist_dist] using hsep (hF ha) (hF hb) hab
  exact closedBall_disjoint_closedBall ((add_halves (ε : ℝ)).symm ▸ this)

lemma iUnion_closedBall_subset_closedBall {α : Type*} [PseudoMetricSpace α] {x : α} {R r : ℝ}
    {s : Set α} (hs : s ⊆ closedBall x R) :
    (⋃ c ∈ s, closedBall c r) ⊆ closedBall x (R + r) := by
  refine Set.iUnion₂_subset fun c hc ↦ closedBall_subset_closedBall' ?_
  have : dist c x ≤ R := mem_closedBall.1 (hs hc)
  linarith

section VolumetricBound
open Module MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {x : E} {R : ℝ} {ε : ℝ≥0} {C : Set E}

lemma card_mul_addHaar_closedBall_center {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ] (F : Finset E) (r : ℝ) :
    (F.card : ℝ≥0∞) * μ (closedBall 0 r) =
      ∑ c ∈ F, μ (closedBall c r) := by
  rw [Finset.sum_congr rfl fun c _ ↦ μ.addHaar_closedBall_center c r,
    Finset.sum_const, nsmul_eq_mul]

lemma card_le_of_card_mul_volume_le [MeasurableSpace E] (μ : Measure E) [BorelSpace E]
    [Measure.IsAddHaarMeasure μ] (hε : 0 < ε) (hR : 0 ≤ R) (F : Finset E)
    (h : (F.card : ℝ≥0∞) * μ (closedBall 0 (ε / 2)) ≤
      μ (closedBall x (R + ε / 2))) :
    (F.card : ℝ) ≤ ((2 * R + ε) / ε) ^ finrank ℝ E := by
  rw [μ.addHaar_closedBall' x (add_nonneg hR (div_nonneg (NNReal.coe_nonneg ε) zero_le_two)),
    μ.addHaar_closedBall' (0 : E) (div_nonneg (NNReal.coe_nonneg ε) zero_le_two),
    ← mul_assoc,
    ENNReal.mul_le_mul_iff_left (measure_closedBall_pos μ 0 one_pos).ne'
      measure_closedBall_lt_top.ne,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg F.card),
    ENNReal.ofReal_le_ofReal_iff
      (pow_nonneg (add_nonneg hR (div_nonneg (NNReal.coe_nonneg ε) zero_le_two)) _)] at h
  exact ((le_div_iff₀ (pow_pos (half_pos (NNReal.coe_pos.mpr hε)) _)).mpr h).trans_eq
    (div_pow_add_half R ε (finrank ℝ E))

lemma IsSeparated.finset_card_le_of_subset_closedBall {F : Finset E}
    (hsep : IsSeparated ε (F : Set E)) (hε : 0 < ε) (hR : 0 ≤ R)
    (hF : (F : Set E) ⊆ closedBall x R) :
    (F.card : ℝ) ≤ ((2 * R + ε) / ε) ^ finrank ℝ E := by
  classical
  borelize E
  set μ : Measure E := (Module.finBasis ℝ E).addHaar
  have : (F : Set E).PairwiseDisjoint fun c ↦ closedBall c (ε / 2) :=
    hsep.pairwiseDisjoint_closedBall subset_rfl
  have : (F.card : ℝ≥0∞) * μ (closedBall 0 (ε / 2)) ≤
      μ (closedBall x (R + ε / 2)) :=
    calc (F.card : ℝ≥0∞) * μ (closedBall 0 (ε / 2))
        = ∑ c ∈ F, μ (closedBall c (ε / 2)) :=
          card_mul_addHaar_closedBall_center μ F (ε / 2)
      _ = μ (⋃ c ∈ F, closedBall c (ε / 2)) :=
          (measure_biUnion_finset this fun c _ ↦ measurableSet_closedBall).symm
      _ ≤ μ (closedBall x (R + ε / 2)) :=
          measure_mono (iUnion_closedBall_subset_closedBall hF)
  exact card_le_of_card_mul_volume_le μ hε hR F this

lemma IsSeparated.encard_le_of_subset_closedBall (hsep : IsSeparated ε C) (hε : 0 < ε)
    (hR : 0 ≤ R) (hC : C ⊆ closedBall x R) :
    C.encard ≤ ⌊((2 * R + ε) / ε) ^ finrank ℝ E⌋₊ := by
  by_contra h
  rw [not_le] at h
  have : (⌊((2 * R + ε) / ε) ^ finrank ℝ E⌋₊ : ℕ∞) + 1 ≤ C.encard :=
    (ENat.add_one_le_iff (ENat.coe_ne_top _)).2 h
  obtain ⟨D, hDC, hD⟩ := Set.exists_subset_encard_eq this
  have hD_finite : D.Finite := Set.finite_of_encard_eq_coe hD
  have hD_card : hD_finite.toFinset.card = ⌊((2 * R + ε) / ε) ^ finrank ℝ E⌋₊.succ :=
    ENat.coe_inj.1 (hD_finite.encard_eq_coe_toFinset_card.symm.trans hD)
  have hD_subset : (hD_finite.toFinset : Set E) ⊆ C := hD_finite.coe_toFinset.symm ▸ hDC
  exact Nat.not_succ_le_self ⌊((2 * R + ε) / ε) ^ finrank ℝ E⌋₊
    (Nat.le_floor (hD_card ▸
      IsSeparated.finset_card_le_of_subset_closedBall (hsep.mono hD_subset)
        hε hR (hD_subset.trans hC)))

lemma coveringNumber_closedBall_le (hε : 0 < ε) (hR : 0 ≤ R) :
    coveringNumber ε (closedBall x R) ≤ ⌊((2 * R + ε) / ε) ^ finrank ℝ E⌋₊ :=
  (coveringNumber_le_packingNumber ..).trans <|
    packingNumber_le_iff.2 fun _ hP hsep ↦ hsep.encard_le_of_subset_closedBall hε hR hP

end VolumetricBound

end Metric
