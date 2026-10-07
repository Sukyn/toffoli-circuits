import Toffoli.Divide.DivideLayout
import Toffoli.Foundations.WorkspacePreparationCard

namespace Toffoli

/-- Reserve one control for the polarization accumulator. Every preparation
uses the parent pool with that wire removed, so its group of size s has exactly
d+b-s-1 borrowed wires. Wires already excluded from the parent pool remain
excluded, while the groups partition all controls other than the reserved one. -/
theorem mixed_polarization_layout {W : Type*} [DecidableEq W] {d b : ℕ}
    (pool controls : Finset W) (hcontrols : controls ⊆ pool)
    (hcard : controls.card = d) (hpool : pool.card = d + b)
    (hd : 0 < d) (c : Composition (d - 1)) :
    ∃ first ∈ controls, ∃ groups : Fin c.length → Finset W,
      (∀ j, (groups j).card = c.blocksFun j) ∧
      (∀ j, groups j ⊆ pool.erase first) ∧
      Pairwise (fun i j => Disjoint (groups i) (groups j)) ∧
      Finset.univ.biUnion groups = controls.erase first ∧
      ∀ j, (pool.erase first).card =
          c.blocksFun j + (d + b - c.blocksFun j - 1) ∧
        (pool.erase first \ groups j).card = d + b - c.blocksFun j - 1 := by
  classical
  subst d
  obtain ⟨first, hfirst, groups, hcards, hfirstNot, hsubset, hdisjoint, hcover⟩ :=
    divide_layout controls (Finset.card_pos.mp hd) c
  have hchild (j : Fin c.length) : groups j ⊆ pool.erase first :=
    Finset.subset_erase.mpr ⟨(hsubset j).trans hcontrols, hfirstNot j⟩
  have hborrowed (j : Fin c.length) :
      (pool.erase first \ groups j).card =
        controls.card + b - c.blocksFun j - 1 := by
    -- The preparation target is available to the parent but outside this group.
    rw [workspace_preparation_card pool (groups j) ((hsubset j).trans hcontrols)
      first (Finset.mem_sdiff.mpr ⟨hcontrols hfirst, hfirstNot j⟩), hpool, hcards j]
  refine ⟨first, hfirst, groups, hcards, hchild, hdisjoint, hcover, ?_⟩
  intro j
  refine ⟨?_, hborrowed j⟩
  -- The child pool consists of its controls and exactly that many borrowed wires.
  calc
    (pool.erase first).card =
        (groups j).card + (pool.erase first \ groups j).card := by
      rw [add_comm, Finset.card_sdiff_add_card_eq_card (hchild j)]
    _ = c.blocksFun j + (controls.card + b - c.blocksFun j - 1) := by
      rw [hcards j, hborrowed j]

end Toffoli
