module

public import Mathlib.MeasureTheory.Integral.Average

public section

open scoped BigOperators

namespace MeasureTheory
variable {α E : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {s : Set α} {f g : α → E}

@[to_fun average_fun_add]
lemma average_add (hf : Integrable f μ) (hg : Integrable g μ) :
    ⨍ a, (f + g) a ∂μ = ⨍ a, f a ∂μ + ⨍ a, g a ∂μ := by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  · exact integral_add (hf.smul_measure <| by simpa) (hg.smul_measure <| by simpa)

@[to_fun setAverage_fun_add]
lemma setAverage_add (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) :
    ⨍ a in s, (f + g) a ∂μ = ⨍ a in s, f a ∂μ + ⨍ a in s, g a ∂μ := average_add hf hg

lemma average_const_mul {L : Type*} [RCLike L] (r : L) (f : α → L) :
    ⨍ a, r * f a ∂μ = r * ⨍ a, f a ∂μ := integral_const_mul ..

@[simp] lemma average_count [Module ℚ≥0 E] [CompleteSpace E] [MeasurableSingletonClass α]
    [Fintype α] (f : α → E) : ⨍ a, f a ∂.count = 𝔼 a, f a := by
  simp [average, Finset.expect, ← NNRat.cast_smul_eq_nnqsmul ℝ]

variable [PartialOrder E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [ClosedIciTopology E]

/-- The average of a function which is nonnegative almost everywhere is nonnegative. -/
lemma average_nonneg_of_ae (hf : 0 ≤ᵐ[μ] f) : 0 ≤ ⨍ a, f a ∂μ :=
  integral_nonneg_of_ae <| hf.filter_mono <| Measure.ae_smul_measure_le _

lemma average_nonneg (hf : 0 ≤ f) : 0 ≤ ⨍ a, f a ∂μ := integral_nonneg hf

end MeasureTheory
