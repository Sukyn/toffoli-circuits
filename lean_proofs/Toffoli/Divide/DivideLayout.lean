import Toffoli.Divide.CompositionPartition

namespace Toffoli

/-- Reserve one control, then place the blocks of a composition on all the
remaining controls. The groups use the original wire indices, have their
prescribed sizes, and partition exactly the controls other than `first`. -/
theorem divide_layout {W : Type*} [DecidableEq W] (controls : Finset W)
    (hne : controls.Nonempty) (c : Composition (controls.card - 1)) :
    ∃ first ∈ controls, ∃ groups : Fin c.length → Finset W,
      (∀ i, (groups i).card = c.blocksFun i) ∧
      (∀ i, first ∉ groups i) ∧
      (∀ i, groups i ⊆ controls) ∧
      Pairwise (fun i j => Disjoint (groups i) (groups j)) ∧
      Finset.univ.biUnion groups = controls.erase first := by
  classical
  obtain ⟨first, hfirst⟩ := hne
  obtain ⟨groups, hcards, hsubset, hdisjoint, hcover⟩ :=
    composition_partition (controls.erase first) (Finset.card_erase_of_mem hfirst) c
  exact ⟨first, hfirst, groups, hcards,
    fun i => (Finset.subset_erase.mp (hsubset i)).2,
    fun i => (Finset.subset_erase.mp (hsubset i)).1, hdisjoint, hcover⟩

end Toffoli
