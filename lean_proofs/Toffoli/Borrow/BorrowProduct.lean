import Toffoli.Borrow.BorrowProductTrace
import Toffoli.Borrow.BorrowWorkspace
import Toffoli.Borrow.IndexedProduct
import Toffoli.Polarization.IndexedToffoli

namespace Toffoli

/-- The paper's Borrow construction on the original controls. The balanced
partition supplies the temporary wires; every preparation restores its own
workspace, and the outer trace restores both designated controls. The same
construction and exact count apply to every coefficient, including zero. -/
theorem borrow_product {p d : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hd : 3 ≤ d)
    (μ : ZMod p) :
    ∃ c : MultiCircuit (ZMod p) d,
      c.Realizes (fun x => μ * ∏ i, x i) ∧
      c.cost = 3 * binaryLadderCost (2 * optimalSquareCost p hp) ((d + 1) / 2) +
        4 * binaryLadderCost (2 * optimalSquareCost p hp) (d / 2) +
        4 * (2 * optimalSquareCost p hp) := by
  classical
  obtain ⟨w⟩ := borrow_workspace d hd
  have hyF : w.y ∉ w.groupF := Finset.disjoint_right.mp w.groups_disjoint w.y_mem
  have hzG : w.z ∉ w.groupYH := Finset.disjoint_left.mp w.groups_disjoint w.z_mem
  have hyz : w.y ≠ w.z := fun h => hzG (h ▸ w.y_mem)
  -- Each ladder borrows only from the opposite group, excluding its target.
  have hleft : Disjoint w.groupF w.workspaceF :=
    Finset.disjoint_of_subset_right
      (w.workspaceF_subset.trans (Finset.erase_subset _ _)) w.groups_disjoint
  have hright : Disjoint w.groupYH w.workspaceYH :=
    Finset.disjoint_of_subset_right
      (w.workspaceYH_subset.trans (Finset.erase_subset _ _)) w.groups_disjoint.symm
  have htargetF : ∀ i ∈ w.groupF ∪ w.workspaceF, some w.y ≠ some i := by
    have houtside : w.y ∉ w.groupF ∪ w.workspaceF :=
      Finset.notMem_union.mpr ⟨hyF,
        Finset.notMem_mono w.workspaceF_subset (Finset.notMem_erase _ _)⟩
    intro i hi
    simpa only [ne_eq, Option.some.injEq] using (ne_of_mem_of_not_mem hi houtside).symm
  have htargetG : ∀ i ∈ w.groupYH ∪ w.workspaceYH, some w.z ≠ some i := by
    have houtside : w.z ∉ w.groupYH ∪ w.workspaceYH :=
      Finset.notMem_union.mpr ⟨hzG,
        Finset.notMem_mono w.workspaceYH_subset (Finset.notMem_erase _ _)⟩
    intro i hi
    simpa only [ne_eq, Option.some.injEq] using (ne_of_mem_of_not_mem hi houtside).symm
  have h2 : (2 : ZMod p) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (ZMod p) Nat.prime_two (show p ≠ 2 by omega)
  have h4 : (4 : ZMod p) ≠ 0 := by
    simpa only [show (4 : ZMod p) = 2 * 2 by norm_num] using mul_ne_zero h2 h2
  -- Fix each group's wire layout once; only the scalar changes between calls.
  have constructF :=
    indexed_product hp w.groupF w.workspaceF ⟨w.z, w.z_mem⟩
      (by rw [w.workspaceF_card, w.groupF_card]) hleft (some w.y) htargetF
  have constructG :=
    indexed_product hp w.groupYH w.workspaceYH ⟨w.y, w.y_mem⟩
      (by rw [w.workspaceYH_card, w.groupYH_card]) hright (some w.z) htargetG
  obtain ⟨prepareF, hprepareF, hprepareF_cost⟩ := constructF 1
  obtain ⟨middleF, hmiddleF, hmiddleF_cost⟩ := constructF (-2)
  obtain ⟨prepareG, hprepareG, hprepareG_cost⟩ := constructG 1
  obtain ⟨undoG, hundoG, hundoG_cost⟩ := constructG (-1)
  obtain ⟨positive, hpositive, hpositive_cost, _⟩ :=
    indexed_toffoli hp w.y w.z hyz none (by simp) (by simp) (μ / 4)
  obtain ⟨negative, hnegative, hnegative_cost, _⟩ :=
    indexed_toffoli hp w.y w.z hyz none (by simp) (by simp) (-(μ / 4))
  simp only [indexedTargetAdd] at hpositive hnegative
  obtain ⟨hrealizes, hcost⟩ := borrow_product_trace w.groupF w.groupYH
    w.groups_disjoint w.y w.z w.y_mem w.z_mem μ h4
    prepareF middleF prepareG undoG positive negative
    (by simpa only [indexedTargetAdd, one_mul] using hprepareF)
    (by simpa only [indexedTargetAdd] using hmiddleF)
    (by simpa only [indexedTargetAdd, one_mul] using hprepareG)
    (by simpa only [indexedTargetAdd, neg_one_mul, sub_eq_add_neg] using hundoG)
    hpositive hnegative
  have hproduct (x : Controls (ZMod p) d) :
      (∏ i ∈ w.groupF, x i) * (∏ i ∈ w.groupYH, x i) = ∏ i, x i := by
    rw [← Finset.prod_union w.groups_disjoint, w.groups_cover]
  refine ⟨borrowProductCircuit prepareF middleF prepareG undoG positive negative, ?_, ?_⟩
  · simpa only [mul_assoc, hproduct] using hrealizes
  · rw [hcost, hprepareF_cost, hmiddleF_cost, hprepareG_cost, hundoG_cost,
      hpositive_cost, hnegative_cost, w.groupF_card, w.groupYH_card]
    omega

end Toffoli
