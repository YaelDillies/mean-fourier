module

public import Mathlib.Analysis.Normed.Group.Bounded
public import MeanFourier.Mathlib.Topology.Bornology.Basic

public section

open Bornology

variable {α E : Type*} [NormedGroup E] {f : α → E}

@[to_additive isBddFun_iff_exists_forall_norm_le]
lemma isBddFun_iff_exists_forall_norm_le' : IsBddFun f ↔ ∃ C, ∀ x, ‖f x‖ ≤ C := by
  simp [IsBddFun, isBounded_iff_forall_norm_le']

alias ⟨Bornology.IsBddFun.exists_forall_norm_le, _⟩ := isBddFun_iff_exists_forall_norm_le

@[to_additive existing Bornology.IsBddFun.exists_forall_norm_le]
alias ⟨Bornology.IsBddFun.exists_forall_norm_le', _⟩ := isBddFun_iff_exists_forall_norm_le'
