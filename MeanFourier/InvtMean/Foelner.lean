/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import MeanFourier.InvtMean.Defs
public import MeanFourier.Mathlib.Algebra.BigOperators.Expect
public import MeanFourier.Mathlib.MeasureTheory.Integral.Average
public import MeanFourier.Mathlib.MeasureTheory.Group.FoelnerFilter
public import MeanFourier.Mathlib.MeasureTheory.Measure.Count

/-!
# The Foelner mean associated to a Foelner filter
-/

public section

open Bornology Filter MeasureTheory
open scoped ComplexOrder Indicator Topology

namespace InvtMean
variable {G ι : Type*} [MeasurableSpace G] [Group G]
  {μ : Measure G} {l : Filter ι} [l.NeBot] {F : ι → Set G}

variable (μ l F) (hF : IsFoelner G μ l F) in
@[expose]
noncomputable def foelner : InvtMean G where
  IsMeasFun f := IsBddFun f ∧ ∃ z, Tendsto (fun i ↦ ⨍ x in F i, f x ∂ μ) l (𝓝 z)
  isBddFun_of_isMeasFun f hf := hf.1
  isMeasFun_const z := by
    refine ⟨⟨‖z‖, by simp⟩, z, tendsto_nhds_of_eventually_eq ?_⟩
    filter_upwards [hF.eventually_meas_ne_zero, hF.eventually_meas_ne_top] with i hi₀ hi
    simp [setAverage_const, hi₀, hi]
  isMeasFun_add := by
    rintro f ⟨hf, w, hw⟩ g ⟨hg, z, hz⟩
    refine ⟨hf.add hg, w + z, ?_⟩
    convert hw.add hz with i
    rw [setAverage_add]
    all_goals sorry
  isMeasFun_smul := by
    rintro w f ⟨hf, z, hz⟩
    exact ⟨hf.const_smul, w * z, by simpa [average_const_mul] using hz.const_smul w⟩
  isMeasFun_translate := by
    rintro g f ⟨hf, z, hr⟩
    refine ⟨?_, z, ?_⟩
    all_goals sorry
  toFun f := limUnder l fun i ↦ ⨍ x in F i, f x ∂ μ
  map_zero := Tendsto.limUnder_eq <| by simp
  map_add := by
    rintro f₁ ⟨-, z, hr⟩ f₂ ⟨-, s, hs⟩
    rw [hr.limUnder_eq, hs.limUnder_eq]
    refine ((hr.add hs).congr' ?_).limUnder_eq
    filter_upwards [hF.eventually_meas_ne_zero, hF.eventually_meas_ne_top] with i hi₀ hi
    rw [setAverage_add (.of_bound _ _ _ _) (.of_bound _ _ _ _)]
    all_goals sorry
  map_smul := by
    rintro f ⟨-, z, hr⟩ z
    simpa [hr.limUnder_eq, average_const_mul, mul_div_assoc] using (hr.const_smul z).limUnder_eq
  map_nonneg := by
    rintro f hf ⟨-, z, hr⟩
    rw [hr.limUnder_eq]
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hr <| .of_forall fun i ↦ average_nonneg hf
  map_translate := by
    rintro f ⟨-, z, hr⟩ g
    rw [hr.limUnder_eq]
    sorry

@[simp high] lemma foelner_count_indicator_one_finset [MeasurableSingletonClass G] [Fintype G]
    (A : Finset G) :
    foelner .count l (fun _ ↦ .univ) .univ_of_isFiniteMeasure 𝟭_[(A : Set G)] = A.dens := by
  classical simp [foelner, tendsto_const_nhds.limUnder_eq]

@[simp] lemma foelner_count_indicator_one [MeasurableSingletonClass G] [Fintype G] (A : Set G) :
    foelner .count l (fun _ ↦ .univ) .univ_of_isFiniteMeasure 𝟭_[(A : Set G)] =
      A.toFinite.toFinset.dens := by lift A to Finset G using A.toFinite; simp

@[simp]
protected lemma IsMeasFun.foelner_of_discrete [MeasurableSingletonClass G] [Finite G] {hF}
    {f : G → ℂ} : (foelner μ l F hF).IsMeasFun f := by
  refine ⟨.of_finite, ⨍ x, f x ∂μ, tendsto_nhds_of_eventually_eq ?_⟩
  sorry

@[simp]
protected lemma IsMeasSet.foelner_of_discrete [MeasurableSingletonClass G] [Finite G] {hF}
    {s : Set G} : (foelner μ l F hF).IsMeasSet s := IsMeasFun.foelner_of_discrete ..

end InvtMean
