import Toffoli.Mixed.MixedLadderLayoutModel
import Toffoli.Divide.CompositionPartition

namespace Toffoli

/-- Every numerical ladder grouping can be allocated on the original
available wires. Mathlib's block equivalence partitions the controls;
the workspace inequality supplies distinct dirty wires between the groups. -/
theorem mixed_ladder_layout {n d b : ℕ} (L : MixedLadder d b)
    (controls pool : Finset (Fin n)) (hsubset : controls ⊆ pool)
    (hcontrols : controls.card = d) (hpool : pool.card = d + b) :
    Nonempty (MixedLadderLayout L controls pool) := by
  classical
  obtain ⟨groups, hcards, hgroups, hdisjoint, hcover⟩ :=
    composition_partition controls hcontrols L.groups
  -- Choose the required distinct dirty wires from the rest of the pool.
  have hborrowed : (pool \ controls).card = b := by
    rw [Finset.card_sdiff_of_subset hsubset, hpool, hcontrols]
    omega
  let borrowedIndex : ↥(pool \ controls) ≃ Fin b := Finset.equivFinOfCardEq hborrowed
  let dirtyIndex : Fin (L.groups.length - 1) ↪ ↥(pool \ controls) :=
    (Fin.castLEEmb L.workspace).trans borrowedIndex.symm.toEmbedding
  exact ⟨{ controls_subset := hsubset, controls_card := hcontrols, pool_card := hpool
           groups := groups, group_card := hcards, group_subset := hgroups
           groups_disjoint := hdisjoint, groups_cover := hcover
           dirty := dirtyIndex.trans ⟨Subtype.val, Subtype.val_injective⟩
           dirty_mem := fun j => (dirtyIndex j).property }⟩

end Toffoli
