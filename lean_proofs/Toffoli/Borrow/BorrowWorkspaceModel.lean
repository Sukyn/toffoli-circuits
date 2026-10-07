import Mathlib.Data.Fintype.Card

namespace Toffoli

/-- Original control-wire indices for the balanced Borrow construction.
The groups represent F and yH. Their two ladders borrow from the opposite
group, excluding the call's target y or z. No extra wire is introduced. -/
structure BorrowWorkspace (d : ℕ) where
  groupF : Finset (Fin d)
  groupYH : Finset (Fin d)
  y : Fin d
  z : Fin d
  workspaceF : Finset (Fin d)
  workspaceYH : Finset (Fin d)
  groupF_card : groupF.card = (d + 1) / 2
  groupYH_card : groupYH.card = d / 2
  groups_disjoint : Disjoint groupF groupYH
  groups_cover : groupF ∪ groupYH = Finset.univ
  y_mem : y ∈ groupYH
  z_mem : z ∈ groupF
  workspaceF_subset : workspaceF ⊆ groupYH.erase y
  workspaceF_card : workspaceF.card = (d + 1) / 2 - 2
  workspaceYH_subset : workspaceYH ⊆ groupF.erase z
  workspaceYH_card : workspaceYH.card = d / 2 - 2

end Toffoli
