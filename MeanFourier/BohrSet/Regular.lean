/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import MeanFourier.BohrSet.Defs

/-!
# Regular Bohr sets
-/

public section

open AddChar Complex Function
open scoped NNReal

namespace BohrSet
variable {G : Type*} [Group G] {B : BohrSet G} {x : G} {ρ ε : ℝ}

/-- A Bohr set `B` is *regular* if the dilates of `B` by numbers close to `1` are of comparable size
to `B`. -/
structure IsRegular (B : BohrSet G) : Prop where
  le_card_smul (κ : ℝ) (hκ₀ : 0 ≤ κ) (hκ : κ ≤ B.dimSqRank / 100) :
    (1 - 100 * B.dimSqRank * κ) * Nat.card B ≤ Nat.card ↥((1 - κ) • B)
  card_smul_le (κ : ℝ) (hκ₀ : 0 ≤ κ) (hκ : κ ≤ B.dimSqRank / 100) :
    Nat.card ↥((1 + κ) • B) ≤ (1 + 100 * B.dimSqRank * κ) * Nat.card B

/-- **Bohr Set Regularity**. Any Bohr set can be dilated by a small amount to become a regular Bohr
set. -/
lemma regularity (B : BohrSet G) (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    ∃ ρ : ℝ, ε ≤ ρ ∧ ρ ≤ 2 * ε ∧ (ρ • B).IsRegular := by
  sorry

end BohrSet
