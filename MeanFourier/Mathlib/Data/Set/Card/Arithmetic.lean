module

public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.Data.Nat.Choose.Basic
public import MeanFourier.Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Powerset
public import MeanFourier.Mathlib.Order.Interval.Finset.Basic

public section

namespace Set
variable {α : Type*} {A : Set α} {d : ℕ}

private lemma setOf_subset_and_ncard_le_zero (hA : A.Finite) :
    {B | B ⊆ A ∧ B.ncard ≤ 0} = {∅} := by
  ext B; simp +contextual [and_or_left, and_iff_right_of_imp, hA.subset]

variable (A d) in
private lemma setOf_subset_and_ncard_le_succ :
    {B | B ⊆ A ∧ B.ncard ≤ d + 1} = {B | B ⊆ A ∧ B.ncard ≤ d} ∪ {B ⊆ A | B.ncard = d + 1} := by
  ext B; simp only [mem_ofPred_eq, mem_union]; lia

variable (A d) in
private lemma disjoint_setOf_ncard_le_setOf_ncard_eq :
    Disjoint {B | B ⊆ A ∧ B.ncard ≤ d} {B ⊆ A | B.ncard = d + 1} := by grind

/-- A finite set `A` has `∑ k ≤ d, A.ncard.choose k` subsets of size at most `d`. -/
lemma ncard_setOf_ncard_le (hA : A.Finite) (d : ℕ) :
    {B | B ⊆ A ∧ B.ncard ≤ d}.ncard = ∑ k ∈ .Iic d, A.ncard.choose k := by
  induction d with
  | zero => rw [setOf_subset_and_ncard_le_zero hA, ncard_singleton, Finset.Iic_zero,
      Finset.sum_singleton, Nat.choose_zero_right]
  | succ d ihd =>
    rw [setOf_subset_and_ncard_le_succ,
      ncard_union_eq (disjoint_setOf_ncard_le_setOf_ncard_eq ..)
        (hA.finite_subsets.subset fun _B hB ↦ hB.1)
          (hA.finite_subsets.subset fun _B hB ↦ hB.1), ihd,
      ncard_powerset_ncard hA, Finset.sum_Iic_add_zero]

end Set
