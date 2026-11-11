module

public import Mathlib.Combinatorics.Additive.CovBySMul
public import Mathlib.Topology.MetricSpace.CoveringNumbers

public section

open Metric
open scoped Finset Pointwise NNReal ENNReal

variable {G X : Type*} [Group G]

section PseudoMetricSpace
variable [PseudoMetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] {K : ℝ} {ε : ℝ}

@[simp]
lemma univ_closedBall_one (hε : 0 ≤ ε) :
    CovBySMul G K .univ (closedBall (1 : G) ε) ↔
      (coveringNumber ε.toNNReal (.univ : Set G) : EReal) ≤ K := by
  sorry

end PseudoMetricSpace
