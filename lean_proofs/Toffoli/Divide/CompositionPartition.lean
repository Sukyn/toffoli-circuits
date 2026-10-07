import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.EquivFin

namespace Toffoli

/-- Partition a finite set into the ordered block sizes of a composition.
Mathlib identifies the block positions with `Fin d`; a bijection with the
given set places every element in exactly one block. -/
theorem composition_partition {α : Type*} [DecidableEq α] {d : ℕ}
    (s : Finset α) (hcard : s.card = d) (c : Composition d) :
    ∃ groups : Fin c.length → Finset α,
      (∀ i, (groups i).card = c.blocksFun i) ∧
      (∀ i, groups i ⊆ s) ∧
      Pairwise (fun i j => Disjoint (groups i) (groups j)) ∧
      Finset.univ.biUnion groups = s := by
  classical
  let index : (Σ i : Fin c.length, Fin (c.blocksFun i)) ≃ s :=
    c.blocksFinEquiv.trans (Finset.equivFinOfCardEq hcard).symm
  let wire (a : Σ i : Fin c.length, Fin (c.blocksFun i)) : α := (index a).val
  have hinjective : Function.Injective wire := Subtype.val_injective.comp index.injective
  let groups (i : Fin c.length) := Finset.univ.image (fun j => wire ⟨i, j⟩)
  have hsubset (i : Fin c.length) : groups i ⊆ s :=
    Finset.image_subset_iff.mpr (fun j _ => (index ⟨i, j⟩).property)
  refine ⟨groups, ?_, hsubset, ?_, ?_⟩
  · intro i
    have hi : Function.Injective (fun j : Fin (c.blocksFun i) => wire ⟨i, j⟩) :=
      hinjective.comp sigma_mk_injective
    dsimp only [groups]
    rw [Finset.card_image_of_injective _ hi]
    simp
  · -- Distinct blocks cannot share an element of the global indexing.
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
    exact hij (congrArg Sigma.fst (hinjective (ha.trans hb.symm)))
  · -- Surjectivity puts every element of the set into one of the blocks.
    apply Finset.Subset.antisymm
    · exact Finset.biUnion_subset.mpr (fun i _ => hsubset i)
    · intro x hx
      obtain ⟨⟨i, j⟩, h⟩ := index.surjective ⟨x, hx⟩
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨j, Finset.mem_univ _, congrArg Subtype.val h⟩⟩

end Toffoli
