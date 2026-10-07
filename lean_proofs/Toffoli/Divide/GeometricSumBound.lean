import Mathlib.Algebra.Ring.GeomSum

namespace Toffoli
open scoped BigOperators

/-- When each level is at least twice as large as the preceding one,
all levels together cost less than twice the last level. -/
theorem geometric_sum_bound {W : ℕ} (hW : 2 ≤ W) (h : ℕ) :
    (∑ i ∈ Finset.range (h + 1), W ^ i) + 1 ≤ 2 * W ^ h := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_range_succ]
    -- The previous levels, including their unit margin, fit in the new last level.
    have hlast : 2 * W ^ h ≤ W ^ (h + 1) := by
      simpa [pow_succ, Nat.mul_comm] using Nat.mul_le_mul_right (W ^ h) hW
    omega

end Toffoli
