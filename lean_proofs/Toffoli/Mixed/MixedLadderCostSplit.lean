import Mathlib.Algebra.BigOperators.Fin

namespace Toffoli
open scoped BigOperators

/-- Separate a ladder's two endpoint costs from its interior costs.
There may be no interior stages: the formula also covers a two-group ladder. -/
theorem mixed_ladder_cost_split (k : ℕ) (q : Fin (k + 2) → ℕ) :
    (∑ j : Fin (k + 2), (if j.val = 0 ∨ j.val + 1 = k + 2 then 2 else 4) * q j) =
      2 * q 0 + 4 * (∑ j : Fin k, q j.castSucc.succ) +
        2 * q (Fin.last (k + 1)) := by
  -- Split off the first and last calls; every remaining index is internal.
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have hnotlast (j : Fin k) : j.val ≠ k := Nat.ne_of_lt j.isLt
  simp [Nat.add_assoc, hnotlast, ← Finset.mul_sum]

end Toffoli
