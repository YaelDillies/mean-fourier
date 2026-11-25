module

public import Mathlib.Data.Finset.Lattice.Fold

public section

namespace Pi
variable {α β : Type*} {C : β → Type*}

/-- Unapplied form of `Finset.sup'_apply`, tagged `push ←` so that `@[to_fun]` can eta-expand
`s.sup' H f` into `fun b ↦ s.sup' H fun a ↦ f a b`. -/
@[to_dual (attr := push ←)
/-- Unapplied form of `Finset.inf'_apply`, tagged `push ←` so that `@[to_fun]` can eta-expand
`s.inf' H f` into `fun b ↦ s.inf' H fun a ↦ f a b`. -/]
protected lemma finsetSup'_def [∀ b, SemilatticeSup (C b)] {s : Finset α} (H : s.Nonempty)
    (f : α → ∀ b, C b) : s.sup' H f = fun b ↦ s.sup' H fun a ↦ f a b :=
  funext <| Finset.sup'_apply H f

end Pi
