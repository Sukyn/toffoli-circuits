import Toffoli.Borrow.BinaryLadderCostModel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

namespace Toffoli

/-- Each control contributes at most four Toffoli costs to a binary ladder.
The same bound includes the free SUM and the single-Toffoli base cases. -/
theorem binary_ladder_cost_bound (C2 s : ℕ) :
    binaryLadderCost C2 s ≤ 4 * C2 * s := by
  unfold binaryLadderCost
  split_ifs with hsmall htwo
  · exact Nat.zero_le _
  · subst s
    omega
  · calc
      4 * (s - 2) * C2 = (4 * C2) * (s - 2) := by ring
      _ ≤ 4 * C2 * s := Nat.mul_le_mul_left _ (Nat.sub_le s 2)

end Toffoli
