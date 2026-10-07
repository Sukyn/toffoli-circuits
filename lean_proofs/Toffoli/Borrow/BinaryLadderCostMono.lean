import Toffoli.Borrow.BinaryLadderCostModel
import Mathlib.Order.Monotone.Basic

namespace Toffoli

/-- Adding controls never decreases the binary-ladder cost, including the
free SUM and single-Toffoli cases before the linear ladder formula applies. -/
theorem binary_ladder_cost_mono (C2 : ℕ) : Monotone (binaryLadderCost C2) := by
  -- It suffices to check what happens when one control is added.
  apply monotone_nat_of_le_succ
  intro s
  rcases s with _ | _ | _ | s
  · simp [binaryLadderCost]
  · simp [binaryLadderCost]
  · simpa [binaryLadderCost] using
      Nat.le_mul_of_pos_left C2 (by decide : 0 < 4)
  · simpa [binaryLadderCost] using
      Nat.mul_le_mul_right C2 (Nat.mul_le_mul_left 4 (Nat.le_succ (s + 1)))

end Toffoli
