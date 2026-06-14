/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.Additive.ApproximateSubgroup
public import MeanFourier.Mathlib.Combinatorics.Additive.CovBySMul
public import MeanFourier.Mathlib.Topology.MetricSpace.CoveringNumbers
public import MeanFourier.BohrSet.Defs

/-!
# Dilation estimate for Bohr sets
-/

public section

open AddChar Complex Function
open scoped NNReal

namespace BohrSet
variable {G : Type*} [Group G] {B : BohrSet G} {A : Set G} {x : G} {K ε : ℝ}

/-- **Dilation estimate** for Bohr sets -/
theorem smul_covBySMul (hK : 0 < K) :
    CovBySMul G ((14 * K) ^ B.dimSqRank) (K • B).chordSet B.chordSet := by
  sorry

lemma isApproximateSubgroup_chordSet : IsApproximateSubgroup (28 ^ B.dimSqRank) B.chordSet where
  one_mem := by simp
  inv_eq_self := by simp
  sq_covBySMul := by grw [chordSet_pow_subset]; convert smul_covBySMul _ <;> norm_num

end BohrSet
