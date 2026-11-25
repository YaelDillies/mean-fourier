module

public import Mathlib.Analysis.Normed.Order.Lattice

public section

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]

lemma norm_sup_sub_sup_le (a b c d : E) : ‖a ⊔ c - (b ⊔ d)‖ ≤ ‖a - b‖ + ‖c - d‖ :=
  (norm_sub_le_norm_sub_add_norm_sub _ (b ⊔ c) _).trans <| add_le_add
    (norm_sup_sub_sup_le_norm ..)
    (by rw [sup_comm b c, sup_comm b d]; exact norm_sup_sub_sup_le_norm ..)

lemma norm_inf_sub_inf_le (a b c d : E) : ‖a ⊓ c - (b ⊓ d)‖ ≤ ‖a - b‖ + ‖c - d‖ :=
  (norm_sub_le_norm_sub_add_norm_sub _ (b ⊓ c) _).trans <| add_le_add
    (norm_inf_sub_inf_le_norm ..)
    (by rw [inf_comm b c, inf_comm b d]; exact norm_inf_sub_inf_le_norm ..)

/-- Supremum as a function `⊔ : E × E → E` on a solid normed lattice is `2`-Lipschitz. -/
lemma lipschitzWith_uncurry_sup : LipschitzWith 2 (fun p : E × E ↦ p.1 ⊔ p.2) := by
  refine .of_dist_le_mul fun p q ↦ ?_
  grw [dist_eq_norm, norm_sup_sub_sup_le, NNReal.coe_ofNat, two_mul, Prod.dist_eq]
  grind [dist_eq_norm]

/-- Infimum as a function `⊔ : E × E → E` on a solid normed lattice is `2`-Lipschitz. -/
lemma lipschitzWith_uncurry_inf : LipschitzWith 2 (fun p : E × E ↦ p.1 ⊓ p.2) := by
  refine .of_dist_le_mul fun p q ↦ ?_
  grw [dist_eq_norm, norm_inf_sub_inf_le, NNReal.coe_ofNat, two_mul, Prod.dist_eq]
  grind [dist_eq_norm]

lemma norm_finsetSup'_sub_finsetSup'_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (a b : ι → E) :
    ‖s.sup' hs a - s.sup' hs b‖ ≤ ∑ i ∈ s, ‖a i - b i‖ := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons i s hi hs ih =>
    grw [Finset.sup'_cons hs, Finset.sup'_cons hs, Finset.sum_cons, norm_sup_sub_sup_le, ih]

lemma norm_finsetInf'_sub_finsetInf'_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (a b : ι → E) :
    ‖s.inf' hs a - s.inf' hs b‖ ≤ ∑ i ∈ s, ‖a i - b i‖ := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons i s hi hs ih =>
    grw [Finset.inf'_cons hs, Finset.inf'_cons hs, Finset.sum_cons, norm_inf_sub_inf_le, ih]
