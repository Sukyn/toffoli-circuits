import Toffoli.Foundations.Basic
import Mathlib.Data.Nat.Cast.Field

namespace Toffoli

/-- The exact integer count is the rational expression displayed in the
paper. Divisibility makes the natural-number quotient exact. -/
theorem power_cycle_cost_formula (n r : ℕ) (hdiv : r ∣ n) :
    ((n - n / r : ℕ) : ℚ) = (n : ℚ) * (1 - 1 / (r : ℚ)) := by
  rw [Nat.cast_sub (Nat.div_le_self n r), Nat.cast_div_charZero hdiv]
  ring

end Toffoli
