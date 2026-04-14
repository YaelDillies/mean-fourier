module

public import Mathlib.Analysis.InnerProductSpace.Defs

public section

namespace PUnit
variable {𝕜 : Type*} [RCLike 𝕜]

instance : InnerProductSpace 𝕜 PUnit where
  inner _ _ := 0
  norm_sq_eq_re_inner := by simp
  conj_inner_symm := by simp
  add_left := by simp
  smul_left := by simp

@[simp] lemma inner_eq_zero (x y : PUnit) : inner 𝕜 x y = 0 := rfl

end PUnit
