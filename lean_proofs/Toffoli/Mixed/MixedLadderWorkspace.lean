import Toffoli.Mixed.MixedLadderLayoutModel
import Toffoli.Foundations.WorkspacePreparationCard

namespace Toffoli

/-- Each allocated call has exactly the control and workspace counts in
MixedLadder. Removing an internal target protects it from borrowing; the
last call retains the full pool because its target is the parent's target. -/
theorem mixed_ladder_workspace {n d b : ℕ} {L : MixedLadder d b}
    {controls pool : Finset (Fin n)} (layout : MixedLadderLayout L controls pool)
    (j : Fin L.groups.length) :
    (layout.callControls j).card = L.controls j ∧
      layout.callControls j ⊆ layout.callPool j ∧
      (layout.callPool j).card = L.controls j + L.borrowed j ∧
      (layout.callPool j \ layout.callControls j).card = L.borrowed j := by
  have hdirty (i : Fin (L.groups.length - 1)) : layout.dirty i ∈ pool :=
    (Finset.mem_sdiff.mp (layout.dirty_mem i)).1
  have houtside (i : Fin (L.groups.length - 1)) : layout.dirty i ∉ layout.groups j :=
    fun hi => (Finset.mem_sdiff.mp (layout.dirty_mem i)).2 (layout.group_subset j hi)
  have hcard : (layout.callControls j).card = L.controls j := by
    by_cases hfirst : j.val = 0
    · simpa only [MixedLadderLayout.callControls, dif_pos hfirst,
        MixedLadder.controls, if_pos hfirst, Nat.add_zero] using layout.group_card j
    · simp only [MixedLadderLayout.callControls, dif_neg hfirst,
        MixedLadder.controls, if_neg hfirst]
      rw [Finset.card_insert_of_notMem (houtside _), layout.group_card]
  have hparent : layout.callControls j ⊆ pool := by
    by_cases hfirst : j.val = 0
    · simpa only [MixedLadderLayout.callControls, dif_pos hfirst] using
        (layout.group_subset j).trans layout.controls_subset
    · simp only [MixedLadderLayout.callControls, dif_neg hfirst]
      exact Finset.insert_subset_iff.mpr
        ⟨hdirty _, (layout.group_subset j).trans layout.controls_subset⟩
  -- A call's destination is outside its group and differs from the preceding dirty wire.
  have htarget (hlast : j.val + 1 ≠ L.groups.length) :
      layout.dirty ⟨j.val, by have := j.isLt; omega⟩ ∈ pool \ layout.callControls j := by
    refine Finset.mem_sdiff.mpr ⟨hdirty _, ?_⟩
    by_cases hfirst : j.val = 0
    · simpa only [MixedLadderLayout.callControls, dif_pos hfirst] using houtside
        ⟨j.val, by have := j.isLt; omega⟩
    · simp only [MixedLadderLayout.callControls, dif_neg hfirst,
        Finset.mem_insert, not_or]
      refine ⟨?_, houtside _⟩
      intro heq
      have hindex : j.val = j.val - 1 := congrArg Fin.val (layout.dirty.injective heq)
      omega
  have hsubset : layout.callControls j ⊆ layout.callPool j := by
    by_cases hlast : j.val + 1 = L.groups.length
    · simpa only [MixedLadderLayout.callPool, dif_pos hlast] using hparent
    · simp only [MixedLadderLayout.callPool, dif_neg hlast]
      exact Finset.subset_erase.mpr ⟨hparent, (Finset.mem_sdiff.mp (htarget hlast)).2⟩
  have hborrowed : (layout.callPool j \ layout.callControls j).card = L.borrowed j := by
    by_cases hlast : j.val + 1 = L.groups.length
    · simp only [MixedLadderLayout.callPool, dif_pos hlast,
        MixedLadder.borrowed, if_pos hlast]
      rw [Finset.card_sdiff_of_subset hparent, layout.pool_card, hcard]
    · simp only [MixedLadderLayout.callPool, dif_neg hlast,
        MixedLadder.borrowed, if_neg hlast]
      rw [workspace_preparation_card pool (layout.callControls j) hparent _ (htarget hlast),
        layout.pool_card, hcard]
  refine ⟨hcard, hsubset, ?_, hborrowed⟩
  rw [← hcard, ← hborrowed]
  simpa only [Nat.add_comm] using (Finset.card_sdiff_add_card_eq_card hsubset).symm

end Toffoli
