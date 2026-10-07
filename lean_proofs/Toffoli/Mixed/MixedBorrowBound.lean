import Toffoli.Mixed.MixedCubicBound
import Toffoli.Mixed.MixedCountOne
import Toffoli.Mixed.MixedCountTwo
import Toffoli.Borrow.BinaryLadderCostMono
import Toffoli.Additions.OptimalSquareCostLowerBound
import Toffoli.Borrow.BorrowCostModel
import Mathlib.Tactic.GCongr

namespace Toffoli

/-- The mixed numerical minimum never exceeds Borrow. The balanced cubic
choice uses no larger binary preparations, and Borrow's four final Toffolis
cover the cube additions. SUM and Toffoli give the same base costs. -/
theorem mixed_borrow_bound {p d : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hd : 0 < d) (b : ℕ) :
    mixedCount p hp d b ≤ borrowCost (2 * optimalSquareCost p hp) d := by
  by_cases hone : d = 1
  · simp [hone, mixed_count_one, borrowCost, binaryLadderCost]
  by_cases htwo : d = 2
  · simp [htwo, mixed_count_two, borrowCost, binaryLadderCost]
  let C2 := 2 * optimalSquareCost p hp
  have hpower : 2 * (p - 1) ≤ 4 * C2 := by
    have := optimal_square_cost_lower_bound hp
    dsimp [C2]
    omega
  have hfirst : binaryLadderCost C2 (d / 2) ≤ binaryLadderCost C2 ((d + 1) / 2) :=
    binary_ladder_cost_mono C2 (Nat.div_le_div_right (Nat.le_succ d))
  have hlast : binaryLadderCost C2 ((d - 1) / 2) ≤ binaryLadderCost C2 (d / 2) :=
    binary_ladder_cost_mono C2 (Nat.div_le_div_right (Nat.sub_le d 1))
  calc
    mixedCount p hp d b ≤ 2 * (p - 1) +
        3 * binaryLadderCost C2 (d / 2) +
        4 * binaryLadderCost C2 ((d - 1) / 2) := mixed_cubic_bound hp (by omega) b
    _ ≤ 4 * C2 + 3 * binaryLadderCost C2 ((d + 1) / 2) +
        4 * binaryLadderCost C2 (d / 2) := by gcongr
    _ = borrowCost C2 d := by
      rw [borrowCost, if_neg (by omega : ¬d ≤ 2)]
      ac_rfl

end Toffoli
