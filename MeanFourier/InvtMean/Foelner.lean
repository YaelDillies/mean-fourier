/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Analysis.SpecificLimits.Basic
public import MeanFourier.InvtMean.Defs
public import MeanFourier.Mathlib.Algebra.BigOperators.Expect
public import MeanFourier.Mathlib.MeasureTheory.Group.FoelnerFilter
public import MeanFourier.Mathlib.MeasureTheory.Integral.Average
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
  simp [foelner, tendsto_const_nhds.limUnder_eq, ← Pi.one_def]

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

variable {G : Type*} [Group G] {f : G → ℂ} {x : G}

section Foelner

open Filter
open scoped Pointwise symmDiff Topology

variable {ι : Type*} [DecidableEq G] {g : G → ℂ} {l : Filter ι} {F : ι → Finset G} {Cf Cg : ℝ}

def IsFoelnerNet (l : Filter ι) (F : ι → Finset G) : Prop :=
  (∀ᶠ i in l, (F i).Nonempty) ∧
    ∀ x : G, Tendsto (fun i ↦ (((x • F i) ∆ F i).card : ℝ) / (F i).card) l (𝓝 0)

noncomputable def flatten (T : Finset G) (φ : G → ℂ) : G → ℂ :=
  fun y ↦ (T.card : ℂ)⁻¹ * ∑ x ∈ T, φ (x⁻¹ * y)

omit [DecidableEq G] in
lemma flatten_add (T : Finset G) (φ₁ φ₂ : G → ℂ) :
    flatten T (φ₁ + φ₂) = flatten T φ₁ + flatten T φ₂ := by
  ext
  simp [flatten, Finset.sum_add_distrib, mul_add]

lemma flatten_translate (T : Finset G) (φ : G → ℂ) (z : G) :
    flatten T (τ_[z] φ) = flatten (T.image (· * z)) φ := by
  ext
  simp only [flatten]
  rw [Finset.card_image_of_injective _ (mul_left_injective z)]
  congr 1
  rw [Finset.sum_image (mul_left_injective z).injOn]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp only [translate_apply]
  group

omit [DecidableEq G] in
lemma flatten_mem_convexHull_translates {T : Finset G} (hT : T.Nonempty) (φ : G → ℂ) :
    flatten T φ ∈ convexHull ℝ (translates φ) := by
  have hsum : ∑ _x ∈ T, ((T.card : ℝ))⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ (by exact_mod_cast hT.card_pos.ne')]
  have hmem := Finset.centerMass_mem_convexHull T (w := fun _ ↦ ((T.card : ℝ))⁻¹)
    (z := fun x ↦ τ_[x] φ) (fun i _ ↦ by positivity) (hsum.symm ▸ zero_lt_one)
    (fun x _ ↦ translate_mem_translates φ x)
  have hflat : (∑ x ∈ T, ((T.card : ℝ))⁻¹ • τ_[x] φ) = flatten T φ := by
    ext y
    simp [flatten, ← Finset.mul_sum]
  rwa [Finset.centerMass_eq_of_sum_1 _ _ hsum, hflat] at hmem

omit [DecidableEq G] in
lemma flatten_mem_convexHull_of_mem {T : Finset G} (hT : T.Nonempty) {φ q : G → ℂ}
    (hq : q ∈ convexHull ℝ (translates φ)) :
    flatten T q ∈ convexHull ℝ (translates φ) := by
  classical
  have hlin : IsLinearMap ℝ (flatten T) := by
    constructor
    · exact flatten_add T
    · intro r q
      ext y
      simp only [flatten, Pi.smul_apply, Complex.real_smul, ← Finset.mul_sum]
      ring
  have himg : flatten T q ∈ flatten T '' convexHull ℝ (translates φ) := ⟨q, hq, rfl⟩
  rw [hlin.image_convexHull] at himg
  refine convexHull_min ?_ (convex_convexHull ℝ _) himg
  rintro - ⟨-, ⟨z, rfl⟩, rfl⟩
  rw [flatten_translate]
  exact flatten_mem_convexHull_translates (hT.image _) φ

omit [DecidableEq G] in
lemma norm_le_of_mem_convexHull_translates {φ q : G → ℂ} {C : ℝ}
    (hC : ∀ u, ‖φ u‖ ≤ C) (hq : q ∈ convexHull ℝ (translates φ)) : ∀ u, ‖q u‖ ≤ C := by
  have hconv : Convex ℝ {p : G → ℂ | ∀ v, ‖p v‖ ≤ C} := by
    intro p₁ h₁ p₂ h₂ a b ha hb hab v
    calc
      ‖(a • p₁ + b • p₂) v‖ = ‖a • p₁ v + b • p₂ v‖ := rfl
      _ ≤ ‖a • p₁ v‖ + ‖b • p₂ v‖ := norm_add_le _ _
      _ = a * ‖p₁ v‖ + b * ‖p₂ v‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * C + b * C := by nlinarith [h₁ v, h₂ v]
      _ = C := by grind
  exact convexHull_min (by rintro p ⟨z, rfl⟩ v; simp_all) hconv hq

omit [DecidableEq G] in
lemma norm_flatten_le {T : Finset G} {q : G → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hq : ∀ u, ‖q u‖ ≤ C) (y : G) : ‖flatten T q y‖ ≤ C := by
  rcases T.eq_empty_or_nonempty with rfl | hT
  · simp [flatten, hC]
  have : (0 : ℝ) < T.card := by simp_all
  calc
    ‖flatten T q y‖ ≤ (T.card : ℝ)⁻¹ * ∑ x ∈ T, ‖q (x⁻¹ * y)‖ := by
      rw [flatten, norm_mul, norm_inv]
      gcongr
      · simp
      · exact norm_sum_le _ _
    _ ≤ (T.card : ℝ)⁻¹ * (T.card * C) := by
      gcongr
      simp_rw [← nsmul_eq_mul, ← Finset.sum_const]
      gcongr with x _
      simp_all
    _ = C := by grind

omit [Group G] in
lemma norm_sum_sub_sum_le (A B : Finset G) (φ : G → ℂ) {C : ℝ} (hφ : ∀ u, ‖φ u‖ ≤ C) :
    ‖∑ u ∈ A, φ u - ∑ u ∈ B, φ u‖ ≤ C * (A ∆ B).card := by
  have h1 : ∑ u ∈ A, φ u - ∑ u ∈ B, φ u = ∑ u ∈ A \ B, φ u - ∑ u ∈ B \ A, φ u := by
    rw [← Finset.sum_sdiff (Finset.inter_subset_left (s₁ := A) (s₂ := B)),
      ← Finset.sum_sdiff (Finset.inter_subset_right (s₁ := A) (s₂ := B)),
      Finset.sdiff_inter_self_left, Finset.sdiff_inter_self_right]
    ring
  have h2 : (A ∆ B).card = (A \ B).card + (B \ A).card := by
    rw [symmDiff_def, Finset.sup_eq_union, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
  rw [h1]
  calc
    ‖∑ u ∈ A \ B, φ u - ∑ u ∈ B \ A, φ u‖
      ≤ ‖∑ u ∈ A \ B, φ u‖ + ‖∑ u ∈ B \ A, φ u‖ := norm_sub_le _ _
    _ ≤ (∑ u ∈ A \ B, ‖φ u‖) + ∑ u ∈ B \ A, ‖φ u‖ := by
      gcongr <;> exact norm_sum_le _ _
    _ ≤ (A \ B).card * C + (B \ A).card * C := by
      simp_rw [← nsmul_eq_mul, ← Finset.sum_const]
      gcongr with u _ <;> exact hφ u
    _ = C * (((A \ B).card + (B \ A).card : ℕ) : ℝ) := by grind
    _ = C * (A ∆ B).card := by simp_all

lemma norm_flatten_sub_flatten_le {T : Finset G} {q : G → ℂ} {C : ℝ}
    (hq : ∀ u, ‖q u‖ ≤ C) (y y' : G) :
    ‖flatten T q y - flatten T q y'‖
    ≤ C * ((((y * y'⁻¹) • T) ∆ T).card : ℝ) / T.card := by
  have : 0 ≤ C := le_trans (norm_nonneg _) (hq 1)
  rcases T.eq_empty_or_nonempty with rfl | hT
  · simp [flatten]
  have : (0 : ℝ) < T.card := by simp_all
  have hre : ∑ x ∈ T, q (x⁻¹ * y') = ∑ u ∈ (y * y'⁻¹) • T, q (u⁻¹ * y) := by
    rw [Finset.smul_finset_def]
    simp_rw [smul_eq_mul]
    rw [Finset.sum_image (mul_right_injective (y * y'⁻¹)).injOn]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    · congr 1
      group
  have hflat : flatten T q y - flatten T q y'
      = (T.card : ℂ)⁻¹ * (∑ x ∈ T, q (x⁻¹ * y) - ∑ u ∈ (y * y'⁻¹) • T, q (u⁻¹ * y)) := by
    rw [flatten, flatten, hre]
    ring
  rw [hflat, norm_mul, norm_inv, show ‖(T.card : ℂ)‖ = (T.card : ℝ) from by simp]
  calc
    ((T.card : ℝ))⁻¹ * ‖∑ x ∈ T, q (x⁻¹ * y) - ∑ u ∈ (y * y'⁻¹) • T, q (u⁻¹ * y)‖ ≤
      ((T.card : ℝ))⁻¹ * (C * ((T ∆ ((y * y'⁻¹) • T)).card : ℝ)) := by
      gcongr
      exact norm_sum_sub_sum_le _ _ _ fun u ↦ hq (u⁻¹ * y)
    _ = C * ((((y * y'⁻¹) • T) ∆ T).card : ℝ) / T.card := by grind

omit [Group G] [DecidableEq G] in
lemma exists_mem_of_mem_closure {s : Set (G → ℂ)} {q₀ : G → ℂ} (h : q₀ ∈ closure s)
    (S : Finset G) {ε : ℝ} (hε : 0 < ε) : ∃ q ∈ s, ∀ y ∈ S, ‖q y - q₀ y‖ < ε := by
  have hU : IsOpen {q : G → ℂ | ∀ y ∈ S, ‖q y - q₀ y‖ < ε} := by
    have hrw : {q : G → ℂ | ∀ y ∈ S, ‖q y - q₀ y‖ < ε}
        = ⋂ y ∈ S, (fun q : G → ℂ ↦ q y) ⁻¹' Metric.ball (q₀ y) ε := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Metric.mem_ball, dist_eq_norm]
    rw [hrw]
    exact isOpen_biInter_finset fun y _ ↦ Metric.isOpen_ball.preimage (continuous_apply y)
  obtain ⟨q, hqU, hqs⟩ :=
    mem_closure_iff.1 h _ hU (fun y _ ↦ by simp only [sub_self, norm_zero, hε])
  grind

omit [DecidableEq G] in
lemma exists_add_decomp {q : G → ℂ} (hq : q ∈ convexHull ℝ (translates (f + g))) :
    ∃ qf ∈ convexHull ℝ (translates f), ∃ qg ∈ convexHull ℝ (translates g), q = qf + qg := by
  classical
  rw [convexHull_eq] at hq
  obtain ⟨κ, t, w, z, hw₀, hw₁, hz, rfl⟩ := hq
  choose! X hX using hz
  beta_reduce at hX
  refine ⟨t.centerMass w fun i ↦ τ_[X i] f,
    Finset.centerMass_mem_convexHull t hw₀ (hw₁.symm ▸ zero_lt_one)
      fun i _ ↦ translate_mem_translates f (X i),
    t.centerMass w fun i ↦ τ_[X i] g,
    Finset.centerMass_mem_convexHull t hw₀ (hw₁.symm ▸ zero_lt_one)
      fun i _ ↦ translate_mem_translates g (X i), ?_⟩
  · simp_rw [Finset.centerMass_eq_of_sum_1 _ _ hw₁]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    · rw [← smul_add, ← translate_add_right, hX i hi]

lemma exists_const_limit {J : Type*} (U : Ultrafilter J) {FJ : J → Finset G}
    (hne : ∀ᶠ j in (U : Filter J), (FJ j).Nonempty)
    (hdef : ∀ g₀ : G,
      Tendsto (fun j ↦ (((g₀ • FJ j) ∆ FJ j).card : ℝ) / (FJ j).card) U (𝓝 0))
    {φ : G → ℂ} {C : ℝ} (hC : ∀ u, ‖φ u‖ ≤ C)
    {q : J → G → ℂ} (hq : ∀ j, q j ∈ convexHull ℝ (translates φ)) :
    ∃ z : ℂ, Function.const G z ∈ closure (convexHull ℝ (translates φ)) ∧
      Tendsto (fun j ↦ flatten (FJ j) (q j)) (U : Filter J) (𝓝 (Function.const G z)) := by
  have hC₀ : 0 ≤ C := le_trans (norm_nonneg _) (hC 1)
  have hqb : ∀ j, ∀ u, ‖q j u‖ ≤ C := fun j ↦
    norm_le_of_mem_convexHull_translates hC (hq j)
  have hfb : ∀ j, ∀ y, ‖flatten (FJ j) (q j) y‖ ≤ C := fun j y ↦
    norm_flatten_le hC₀ (hqb j) y
  have hzy : ∀ y : G, ∃ a : ℂ, a ∈ Metric.closedBall (0 : ℂ) C ∧
      Tendsto (fun j ↦ flatten (FJ j) (q j) y) (U : Filter J) (𝓝 a) := by
    intro y
    have hmem : Metric.closedBall (0 : ℂ) C ∈ U.map fun j ↦ flatten (FJ j) (q j) y :=
      Filter.mem_map.2 (Filter.Eventually.of_forall fun j ↦ by
        simp_all)
    obtain ⟨a, ha, hle⟩ := (isCompact_closedBall (0 : ℂ) C).ultrafilter_le_nhds
      (U.map fun j ↦ flatten (FJ j) (q j) y) (Filter.le_principal_iff.2 hmem)
    exact ⟨a, ha, hle⟩
  choose zfun _ hztend using hzy
  have htendsto : Tendsto (fun j ↦ flatten (FJ j) (q j)) (U : Filter J) (𝓝 zfun) :=
    tendsto_pi_nhds.2 fun y ↦ hztend y
  have hmem : zfun ∈ closure (convexHull ℝ (translates φ)) :=
    mem_closure_of_tendsto htendsto
      (hne.mono fun j hj ↦ flatten_mem_convexHull_of_mem hj (hq j))
  have hconst : ∀ y y' : G, zfun y = zfun y' := by
    intro y y'
    have hsub : Tendsto (fun j ↦ flatten (FJ j) (q j) y - flatten (FJ j) (q j) y')
        (U : Filter J) (𝓝 (zfun y - zfun y')) := (hztend y).sub (hztend y')
    have hzero : Tendsto (fun j ↦ flatten (FJ j) (q j) y - flatten (FJ j) (q j) y')
        (U : Filter J) (𝓝 0) := by
      refine squeeze_zero_norm (fun j ↦ norm_flatten_sub_flatten_le (hqb j) y y') ?_
      · have := (hdef (y * y'⁻¹)).const_mul C
        grind
    have := tendsto_nhds_unique hsub hzero
    grind
  have hzc : zfun = Function.const G (zfun 1) := funext fun y ↦ hconst y 1
  grind

lemma IsMenable.eq_mean_add_of_const_mem [l.NeBot] (hf : IsMenable f) (hg : IsMenable g)
    (hFol : IsFoelnerNet l F) (hCf : ∀ u, ‖f u‖ ≤ Cf) (hCg : ∀ u, ‖g u‖ ≤ Cg) {c : ℂ}
    (hc : Function.const G c ∈ closure (convexHull ℝ (translates (f + g)))) :
    c = hf.mean + hg.mean := by
  set L : Filter ((ι × Finset G) × ℕ) := (l ×ˢ atTop) ×ˢ atTop with hLdef
  haveI : L.NeBot := by rw [hLdef]; infer_instance
  have hch : ∀ j : (ι × Finset G) × ℕ, ∃ q ∈ convexHull ℝ (translates (f + g)),
      ∀ y ∈ (F j.1.1)⁻¹ * j.1.2, ‖q y - Function.const G c y‖ < 1 / (j.2 + 1) :=
    fun j ↦ exists_mem_of_mem_closure hc _ (by positivity)
  choose q hqhull hqapp using hch
  choose qf hqf qg hqg hsplit using fun j ↦ exists_add_decomp (hqhull j)
  set FJ : (ι × Finset G) × ℕ → Finset G := fun j ↦ F j.1.1
  have hπ : Tendsto (fun j : (ι × Finset G) × ℕ ↦ j.1.1) L l :=
    tendsto_fst.comp tendsto_fst
  have hneJ : ∀ᶠ j in L, (FJ j).Nonempty := hπ.eventually hFol.1
  have hdefJ : ∀ g₀ : G,
      Tendsto (fun j ↦ (((g₀ • FJ j) ∆ FJ j).card : ℝ) / (FJ j).card) L (𝓝 0) :=
    fun g₀ ↦ (hFol.2 g₀).comp hπ
  obtain ⟨U, hU⟩ := Ultrafilter.exists_le L
  obtain ⟨zf, hzfmem, hzft⟩ :=
    exists_const_limit U (hneJ.filter_mono hU) (fun g₀ ↦ (hdefJ g₀).mono_left hU) hCf hqf
  obtain ⟨zg, hzgmem, hzgt⟩ :=
    exists_const_limit U (hneJ.filter_mono hU) (fun g₀ ↦ (hdefJ g₀).mono_left hU) hCg hqg
  have hsum_t : Tendsto (fun j ↦ flatten (FJ j) (q j)) (U : Filter _)
      (𝓝 (Function.const G (zf + zg))) := by
    have hsplit' : (fun j ↦ flatten (FJ j) (q j))
        = fun j ↦ flatten (FJ j) (qf j) + flatten (FJ j) (qg j) :=
      funext fun j ↦ by rw [hsplit j, flatten_add]
    rw [hsplit']
    exact hzft.add hzgt
  have hsum_c : Tendsto (fun j ↦ flatten (FJ j) (q j)) (U : Filter _)
      (𝓝 (Function.const G c)) := by
    rw [tendsto_pi_nhds]
    intro y
    have h1 : ∀ᶠ S : Finset G in atTop, y ∈ S := by
      filter_upwards [eventually_ge_atTop {y}] with S hS using Finset.singleton_subset_iff.1 hS
    have h2 : ∀ᶠ p : ι × Finset G in l ×ˢ atTop, y ∈ p.2 := tendsto_snd.eventually h1
    have hyS : ∀ᶠ j in L, y ∈ j.1.2 := tendsto_fst.eventually h2
    have hev : ∀ᶠ j in L, ‖flatten (FJ j) (q j) y - c‖ ≤ 1 / (j.2 + 1) := by
      filter_upwards [hyS, hneJ] with j hjS hjne
      have : (0 : ℝ) < (FJ j).card := by simp_all
      have hcard : ((FJ j).card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hjne.card_pos.ne'
      have hkey : flatten (FJ j) (q j) y - c
          = (((FJ j).card : ℂ))⁻¹ * ∑ x ∈ FJ j, (q j (x⁻¹ * y) - c) := by
        rw [flatten, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_sub,
          inv_mul_cancel_left₀ hcard]
      rw [hkey, norm_mul, norm_inv, show ‖((FJ j).card : ℂ)‖ = ((FJ j).card : ℝ) from by simp]
      have hterm : ∀ x ∈ FJ j, ‖q j (x⁻¹ * y) - c‖ ≤ 1 / (j.2 + 1) := by
        intro x hx
        have hmem : x⁻¹ * y ∈ (F j.1.1)⁻¹ * j.1.2 :=
          Finset.mul_mem_mul (Finset.inv_mem_inv hx) hjS
        grind
      calc
        (((FJ j).card : ℝ))⁻¹ * ‖∑ x ∈ FJ j, (q j (x⁻¹ * y) - c)‖
          ≤ (((FJ j).card : ℝ))⁻¹ * ∑ x ∈ FJ j, ‖q j (x⁻¹ * y) - c‖ := by
          gcongr
          exact norm_sum_le _ _
        _ ≤ (((FJ j).card : ℝ))⁻¹ * ∑ x ∈ FJ j, (1 / (j.2 + 1) : ℝ) := by
          gcongr with x hx
          simp_all
        _ = 1 / (j.2 + 1) := by simp_all
    have hto : Tendsto (fun j : (ι × Finset G) × ℕ ↦ 1 / ((j.2 : ℝ) + 1)) L (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp tendsto_snd
    have hdiff : Tendsto (fun j ↦ flatten (FJ j) (q j) y - c) (U : Filter _) (𝓝 0) :=
      squeeze_zero_norm' (hev.filter_mono hU) (hto.mono_left hU)
    have := hdiff.add_const c
    grind
  have heq := tendsto_nhds_unique hsum_t hsum_c
  have hval : zf + zg = c := congrFun heq 1
  rw [← hf.eq_mean hzfmem, ← hg.eq_mean hzgmem]
  simp_all

lemma IsMenable.const_mean_add_mem [l.NeBot] (hf : IsMenable f) (hg : IsMenable g)
    (hFol : IsFoelnerNet l F) (hCf : ∀ u, ‖f u‖ ≤ Cf) (hCg : ∀ u, ‖g u‖ ≤ Cg) :
    Function.const G (hf.mean + hg.mean) ∈
    closure (convexHull ℝ (translates (f + g))) := by
  obtain ⟨U, hU⟩ := Ultrafilter.exists_le l
  have hCfg : ∀ u, ‖(f + g) u‖ ≤ Cf + Cg := fun u ↦
    (norm_add_le _ _).trans (add_le_add (hCf u) (hCg u))
  obtain ⟨z, hzmem, -⟩ := exists_const_limit U (hFol.1.filter_mono hU)
    (fun g₀ ↦ ((hFol.2 g₀).mono_left hU)) hCfg
    (fun _ ↦ subset_convexHull ℝ _ (self_mem_translates (f + g)))
  rwa [hf.eq_mean_add_of_const_mem hg hFol hCf hCg hzmem] at hzmem

protected theorem IsMenable.add [l.NeBot] (hf : IsMenable f) (hg : IsMenable g)
    (hFol : IsFoelnerNet l F) : IsMenable (f + g) :=
  let ⟨Cf, hCf⟩ := hf.exists_norm_le
  let ⟨Cg, hCg⟩ := hg.exists_norm_le
  ⟨⟨Cf + Cg, fun _ ⟨u, hu⟩ ↦ hu ▸ (norm_add_le _ _).trans (add_le_add (hCf u) (hCg u))⟩,
    hf.mean + hg.mean, hf.const_mean_add_mem hg hFol hCf hCg,
    fun _ hw ↦ hf.eq_mean_add_of_const_mem hg hFol hCf hCg hw⟩

theorem IsMenable.mean_add [l.NeBot] (hf : IsMenable f) (hg : IsMenable g)
    (hFol : IsFoelnerNet l F) : (hf.add hg hFol).mean = hf.mean + hg.mean :=
  let ⟨_, hCf⟩ := hf.exists_norm_le
  let ⟨_, hCg⟩ := hg.exists_norm_le
  ((hf.add hg hFol).eq_mean (hf.const_mean_add_mem hg hFol hCf hCg)).symm

end Foelner
