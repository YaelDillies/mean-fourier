module

public import Mathlib.Data.Finset.Pi

public section

namespace Finset
variable {ι : Type*} {α : ι → Type*}
  {s : Finset ι} {t : ∀ i, Finset (α i)} {x : ∀ i, α i}

/- TODO: Rename
* `Finset.pi` to `Finset.piOn`
* `Fintype.piFinset` to `Finset.pi`.
* `Set.pi` to `Set.piOn`.
-/
noncomputable def pi' (s : Finset ι) (t : ∀ i, Finset (α i))
    (ht : ∀ i ∉ s, (t i : Set (α i)).Subsingleton) : Finset (∀ i, α i) := by
  classical
  by_cases ht' : ∃ i ∉ s, t i = ∅
  · exact ∅
  choose x₀ hx₀ using fun i hi ↦
    (ht i hi).eq_empty_or_singleton.resolve_left fun hti ↦ ht' ⟨i, hi, by simpa using hti⟩
  exact (s.pi t).map ⟨fun f i ↦
    if hi : i ∈ s then
      f i hi
    else
      ((ht i hi).eq_empty_or_singleton.resolve_left fun hti ↦
        ht' ⟨i, hi, by simpa using hti⟩).choose,
    fun f g hfg ↦ by ext i hi; simpa [hi] using congr($hfg i)⟩

lemma pi'_of_forall_singleton [DecidableEq ι] (x : ∀ i ∉ s, α i) (ht : ∀ i hi, t i = {x i hi}) :
    s.pi' t (by simp +contextual [ht]) =
      (s.pi t).map ⟨fun f i ↦ if hi : i ∈ s then f i hi else x i hi,
      fun f g hfg ↦ by ext i hi; simpa [hi] using congr($hfg i)⟩ := by
  ext y
  unfold pi'
  rw [dif_neg (by simp +contextual [ht])]
  simp only [mem_map, mem_pi, Function.Embedding.coeFn_mk]
  congr! with z i _ hi
  generalize_proofs h
  simp [ht i hi]

@[simp] lemma mem_pi' (ht) : x ∈ s.pi' t ht ↔ ∀ i, x i ∈ t i := by
  simp only [pi', coe_eq_singleton]
  split_ifs with ht'
  · obtain ⟨i, hi, hti⟩ := ht'
    simp only [notMem_empty, false_iff, not_forall]
    exact ⟨i, by simp [hti]⟩
  simp only [mem_map, mem_pi, Function.Embedding.coeFn_mk]
  refine ⟨?_, fun hx ↦ ⟨fun i _ ↦ x i, fun i _ ↦ hx _, ?_⟩⟩
  · rintro ⟨f, hf, rfl⟩ i
    dsimp
    split_ifs with hi
    · exact hf _ hi
    generalize_proofs h
    rw! [h.choose_spec]
    simp
  · simp only [funext_iff, dite_eq_left_iff]
    rintro i hi
    generalize_proofs h
    exact ht _ hi (by rw! [h.choose_spec]; simp) (hx _)

@[simp] lemma coe_pi' (ht) : (s.pi' t ht : Set (∀ i, α i)) = .pi .univ (fun i ↦ t i) := by ext; simp

end Finset
