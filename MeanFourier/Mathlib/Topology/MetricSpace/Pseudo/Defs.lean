module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

public section

namespace Metric
variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {δ : ℝ → ℝ} {f : X → Y}

attribute [fun_prop] UniformContinuous

variable (δ f) in
/-- A function between metric spaces is uniformly continuous with modulus of continuity `δ : ℝ → ℝ`
if `dist x y ≤ δ(ε) → dist (f x) (f y) ≤ ε` for all `x`, `y`. -/
@[expose, fun_prop]
def IsUniformContinuousWith : Prop :=
  ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ ⦃x y : X⦄, dist x y ≤ δ ε → dist (f x) (f y) ≤ ε

@[fun_prop]
lemma IsUniformContinuousWith.uniformContinuous (hδ : ∀ ε > 0, 0 < δ ε)
    (hf : IsUniformContinuousWith δ f) : UniformContinuous f :=
  uniformContinuous_iff_le.2 fun ε hε ↦ ⟨δ ε, hδ _ hε, hf hε⟩

lemma uniformContinuous_iff_exists_isUniformContinuousWith :
    UniformContinuous f ↔ ∃ δ : ℝ → ℝ, (∀ ε > 0, 0 < δ ε) ∧ IsUniformContinuousWith δ f where
  mp hf := by rw [uniformContinuous_iff_le] at hf; choose! δ hδ hf using hf; exact ⟨δ, hδ, hf⟩
  mpr := by rintro ⟨δ, hδ, hf⟩; fun_prop

end Metric
