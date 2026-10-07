import Toffoli.Borrow.BorrowCostModel
import Toffoli.Borrow.BinaryLadderCostBound
import Toffoli.Additions.OptimalSquareCostBound
import Mathlib.Tactic.GCongr

namespace Toffoli

/-- Borrow has a uniform linear count. The conservative constant forty
covers both balanced ladders, the four final Toffolis, and the base cases. -/
theorem borrow_cost_bound {p d : ℕ} (hp : 5 ≤ p) (hd : 1 ≤ d) :
    borrowCost (2 * optimalSquareCost p hp) d ≤ 40 * p * d := by
  let C2 := 2 * optimalSquareCost p hp
  have hC2 : C2 ≤ 2 * p := by
    have hsquare := optimal_square_cost_bound p hp
    dsimp [C2]
    omega
  have hfamily : borrowCost C2 d ≤ 20 * C2 * d := by
    by_cases hsmall : d ≤ 2
    · rw [borrowCost, if_pos hsmall]
      exact (binary_ladder_cost_bound C2 d).trans
        (by gcongr; omega)
    let a := (d + 1) / 2
    let b := d / 2
    have hsplit : a + b = d := by dsimp [a, b]; omega
    -- Use the larger multiplicity four for both halves of the controls.
    have hleft := binary_ladder_cost_bound C2 a
    have hright := binary_ladder_cost_bound C2 b
    -- The four final Toffolis fit within four additional costs per control.
    have hfinal : 4 * C2 ≤ 4 * C2 * d := by
      simpa using Nat.mul_le_mul_left (4 * C2) hd
    rw [borrowCost, if_neg hsmall]
    change 3 * binaryLadderCost C2 a + 4 * binaryLadderCost C2 b + 4 * C2 ≤ _
    calc
      _ ≤ 4 * (4 * C2 * a) + 4 * (4 * C2 * b) + 4 * C2 := by
        gcongr
        omega
      _ = 16 * C2 * d + 4 * C2 := by rw [← hsplit]; ring
      _ ≤ 16 * C2 * d + 4 * C2 * d := Nat.add_le_add_left hfinal _
      _ = 20 * C2 * d := by ring
  calc
    borrowCost (2 * optimalSquareCost p hp) d ≤ 20 * C2 * d := hfamily
    _ ≤ 20 * (2 * p) * d := by gcongr
    _ = 40 * p * d := by ring

end Toffoli
