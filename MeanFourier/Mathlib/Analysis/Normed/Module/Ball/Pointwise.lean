module

public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import MeanFourier.Mathlib.Topology.Bornology.Basic

public section

namespace Bornology
variable {α 𝕜 E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] {f : α → E}
  {c : 𝕜}

@[to_fun (attr := fun_prop)]
lemma IsBddFun.const_smul (hf : IsBddFun f) : IsBddFun (c • f) := by
  simpa [Pi.smul_def, Set.range_smul, IsBddFun] using hf.smul₀ c

end Bornology
