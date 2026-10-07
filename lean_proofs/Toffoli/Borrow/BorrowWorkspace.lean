import Toffoli.Borrow.BorrowWorkspaceModel

namespace Toffoli

/-- Balanced groups provide actual disjoint workspace selections among the
original controls. For d=3, F has two controls and yH only y; both borrowed
sets are empty because the calls are a Toffoli and a SUM. -/
theorem borrow_workspace (d : ℕ) (hd : 3 ≤ d) : Nonempty (BorrowWorkspace d) := by
  classical
  obtain ⟨F, _, hF⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin d))) (n := (d + 1) / 2) (by simp; omega)
  have hYH : (Fᶜ).card = d / 2 := by
    rw [Finset.card_compl, Fintype.card_fin, hF]
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (show 0 < F.card by omega)
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (show 0 < (Fᶜ).card by omega)
  have hleft : (d + 1) / 2 - 2 ≤ ((Fᶜ).erase y).card := by
    rw [Finset.card_erase_of_mem hy, hYH]
    omega
  have hright : d / 2 - 2 ≤ (F.erase z).card := by
    rw [Finset.card_erase_of_mem hz, hF]
    omega
  obtain ⟨left, hleft_subset, hleft_card⟩ := Finset.exists_subset_card_eq hleft
  obtain ⟨right, hright_subset, hright_card⟩ := Finset.exists_subset_card_eq hright
  exact ⟨{
    groupF := F, groupYH := Fᶜ, y := y, z := z
    workspaceF := left, workspaceYH := right
    groupF_card := hF, groupYH_card := hYH
    groups_disjoint := disjoint_compl_right, groups_cover := by simp
    y_mem := hy, z_mem := hz
    workspaceF_subset := hleft_subset, workspaceF_card := hleft_card
    workspaceYH_subset := hright_subset, workspaceYH_card := hright_card }⟩

end Toffoli
