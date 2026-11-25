module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

public section

open scoped NNReal

/-- Uncurried addition on a seminormed additive group is `2`-Lipschitz. -/
lemma lipschitzWith_uncurry_add {E : Type*} [SeminormedAddCommGroup E] :
    LipschitzWith 2 (fun p : E × E ↦ p.1 + p.2) :=
  LipschitzWith.of_dist_le_mul fun p q ↦ by
    rw [dist_eq_norm, show p.1 + p.2 - (q.1 + q.2) = p.1 - q.1 + (p.2 - q.2) by abel]
    calc ‖p.1 - q.1 + (p.2 - q.2)‖ ≤ ‖p.1 - q.1‖ + ‖p.2 - q.2‖ := norm_add_le ..
      _ ≤ 2 * dist p q := by
          rw [two_mul, Prod.dist_eq, dist_eq_norm, dist_eq_norm]
          gcongr <;> [exact le_max_left ..; exact le_max_right ..]
