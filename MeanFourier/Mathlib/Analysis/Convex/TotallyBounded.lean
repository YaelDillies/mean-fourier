module

public import Mathlib.Analysis.Convex.TotallyBounded

public section

variable (E : Type*) {s : Set E}
variable [AddCommGroup E] [Module ℝ E]
variable [UniformSpace E] [IsUniformAddGroup E] [lcs : LocallyConvexSpace ℝ E] [ContinuousSMul ℝ E]

-- TODO: Replace
@[simp] lemma totallyBounded_convexHull' {s : Set E} :
    TotallyBounded (convexHull ℝ s) ↔ TotallyBounded s where
  mp := .subset <| subset_convexHull ..
  mpr := totallyBounded_convexHull _
