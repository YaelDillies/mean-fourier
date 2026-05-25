module

public import Mathlib.Data.Fintype.Pi
public import MeanFourier.Mathlib.Data.Finset.Pi

public section

namespace Set
variable {ι : Type*} {α : ι → Type*} {t : ∀ i, Set (α i)}

-- TODO: Replace `Set.Finite.pi`
lemma Finite.univ_pi (ht : ∀ i, (t i).Finite) (ht' : {i | (t i).Nontrivial}.Finite) :
    (univ.pi t).Finite := by
  obtain ⟨s, hs⟩ := ht'.exists_finset
  choose t' ht' using fun i ↦ (ht i).exists_finset_coe
  simp only [← not_subsingleton_iff, mem_setOf_eq, iff_not_comm, ← ht'] at hs
  rw [← funext ht', ← Finset.coe_pi' fun i ↦ (hs i).2]
  exact Finset.finite_toSet _

end Set
