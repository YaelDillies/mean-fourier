module

public import Mathlib.Analysis.Normed.Group.Pointwise
public import MeanFourier.Mathlib.Algebra.Group.Pointwise.Set.Basic
public import MeanFourier.Mathlib.Topology.Bornology.Basic

public section

namespace Bornology
variable {α E : Type*} [SeminormedGroup E] {f g : α → E}

-- TODO: How to most efficiently `to_fun` this?
@[to_additive (attr := fun_prop)]
protected nonrec lemma IsBddFun.mul (hf : IsBddFun f) (hg : IsBddFun g) : IsBddFun (f * g) :=
  (hf.mul hg).subset Set.range_mul_subset

end Bornology
