module

public import AddCombi.Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.BigOperators.Expect

import Mathlib.Algebra.BigOperators.Group.Finset.Indicator

public section

open scoped BigOperators Indicator

namespace Finset
variable {ι R : Type*} [DivisionSemiring R] [CharZero R]

@[simp] lemma expect_indicator_one [Fintype ι] (s : Finset ι) : 𝔼 i : ι, 𝟭_[s, R] i = s.dens := by
  classical simp [expect, sum_indicator_eq_sum_inter, NNRat.smul_def, dens, div_eq_inv_mul]

end Finset
