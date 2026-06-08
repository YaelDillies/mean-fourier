/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import MeanFourier.InvtMean.Defs
public import MeanFourier.Mathlib.MeasureTheory.Group.FoelnerFilter
public import MeanFourier.Mathlib.MeasureTheory.Measure.Count

import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The Foelner mean associated to a Foelner filter
-/

public section

open Filter MeasureTheory
open scoped ComplexOrder Indicator Topology

namespace InvtMean
variable {G ι : Type*} [MeasurableSpace G] [Group G]
  {μ : Measure G} {l : Filter ι} [l.NeBot] {F : ι → Set G}

variable (μ l F) (hF : IsFoelner G μ l F) in
@[expose]
noncomputable def foelner : InvtMean G where
  IsMeasFun f :=
    BddAbove (.range (‖f ·‖)) ∧ ∃ r, Tendsto (fun i ↦ (∫ x in F i, f x ∂ μ) / μ.real (F i)) l (𝓝 r)
  bdd_of_isMeasFun f hf := hf.1
  isMeasFun_const z := by
    refine ⟨⟨‖z‖, by simp⟩, z, tendsto_nhds_of_eventually_eq ?_⟩
    filter_upwards [hF.eventually_measureReal_ne_zero] with i hi
    simp [hi]
  isMeasFun_translate := by
    rintro g f ⟨hf, r, hr⟩
    refine ⟨?_, r, ?_⟩
    all_goals sorry
  toFun f := limUnder l (fun i ↦ (∫ x in F i, f x ∂ μ) / μ.real (F i))
  map_zero := Tendsto.limUnder_eq <| by simp
  map_add := by
    rintro f₁ ⟨-, r, hr⟩ f₂ ⟨-, s, hs⟩
    rw [hr.limUnder_eq, hs.limUnder_eq]
    convert (hr.add hs).limUnder_eq using 3 with i
    dsimp
    rw [integral_add, add_div]
    all_goals sorry
  map_smul := by
    rintro f ⟨-, r, hr⟩ z
    simpa [hr.limUnder_eq, integral_const_mul, mul_div_assoc] using (hr.const_smul z).limUnder_eq
  map_nonneg := by
    rintro f hf ⟨-, r, hr⟩
    rw [hr.limUnder_eq]
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hr <| .of_forall fun i ↦
      div_nonneg (integral_nonneg hf) (by positivity)
  map_translate := by
    rintro f ⟨-, r, hr⟩ g
    rw [hr.limUnder_eq]
    sorry

@[simp] lemma foelner_count_indicator_finset [MeasurableSingletonClass G] [Fintype G]
    (A : Finset G) :
    foelner .count l (fun _ ↦ .univ) .univ_of_isFiniteMeasure 𝟭_[(A : Set G)] = A.dens := by
  classical
  simp [foelner, ← Complex.ofReal_sum, Finset.sum_indicator_eq_sum_inter,
    tendsto_const_nhds.limUnder_eq, Finset.dens]

end InvtMean
