/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import MeanFourier.BohrSet.Defs
public import MeanFourier.Mathlib.Combinatorics.Additive.VCDim
public import MeanFourier.InvtMean.Foelner

import MeanFourier.Mathlib.Combinatorics.SetFamily.HausslerPacking

/-!
# Arithmetic regularity for translation-regular dense sets of small VC dimension

This file provides a classification of sort of translation-regular dense sets of small VC dimension
in groups `G` equipped with a Foelner mean `m`.

Precisely, given a group `G` equipped with a Foelner mean `m` and
a translation-regular subset `A` of mean at least `α` and VC dimension at most `d`,
we find a Bohr set `H` of bounded rank and a set `Fᵢ` belonging to the Foelner net such that
one can write `A` as a "thickening" of a set `A' ⊆ A` by `H ∩ Fᵢ`, up to a set of mean at most `ε`.

We provide two important corollaries:
1. When `G` is finite, one can take the trivial Foelner net consisting of many times `G`,
  so that the mean `m` is the density in the usual sense and `H ∩ Fᵢ = H`.
2. When `G = ℝ`, the Foelner sequence of centered growing intervals yields the above result for the
  usual principal value integral.
-/

public section

open MeasureTheory InvtMean
open scoped ComplexOrder Indicator Pointwise symmDiff

variable {G ι : Type*} [Group G] {A : Set G} {α ε : ℝ} {d : ℕ}

theorem arithmetic_regularity_mean_hasMulVCDimLE
    [MeasurableSpace G] {μ : Measure G} {l : Filter ι} [l.NeBot] {F : ι → Set G}
    (hα : 0 < α) (hε : 0 < ε) (hF : IsFoelner G μ l F)
    (hAmeas : (foelner μ l F hF).IsMeasSet A)
    -- (hAreg : (foelner μ l F hF).IsTranslationRegular A)
    (hAdens : α ≤ foelner μ l F hF 𝟭_[A])
    (hAvcdim : HasMulVCDimLE d A) :
    ∃ H : BohrSet G, H.dimRank ≤ (α * ε) ^ (1000 * d) ∧
    ∃ A' ⊆ A, (1 - ε) * foelner μ l F hF 𝟭_[A] ≤ foelner μ l F hF 𝟭_[A'] ∧
    ∀ᶠ i in l, foelner μ l F hF 𝟭_[A ∆ ((F i ∩ H) * A')] ≤ ε := sorry

theorem arithmetic_regularity_finite_hasMulVCDimLE [Fintype G] [DecidableEq G] {A : Finset G}
    (hα : 0 < α) (hε : 0 < ε) (hAdens : α ≤ A.dens)
    (hAvcdim : HasMulVCDimLE d (A : Set G)) :
    ∃ H : BohrSet G, H.dimRank ≤ (α * ε) ^ (1000 * d) ∧
    ∃ A' ⊆ A, (1 - ε) * A.dens ≤ A'.dens ∧ (A ∆ ((H : Set G).toFinite.toFinset * A')).dens ≤ ε := by
  classical
  let : MeasurableSpace G := ⊤
  have : MeasurableSingletonClass G := inferInstance
  obtain ⟨H, hH, A', hA', hA'dens, hA⟩ := arithmetic_regularity_mean_hasMulVCDimLE hα hε
    (μ := .count) (ι := Unit) (l := ⊤) .univ_of_isFiniteMeasure .foelner_of_discrete (by simpa)
      hAvcdim
  lift A' to Finset G using A'.toFinite
  exact ⟨H, hH, A', by simpa, by simpa using hA'dens, by simpa using hA⟩
