import Toffoli.Quadratic.QuadraticModel
import Toffoli.Additions.PowerCycleCostFormula

namespace Toffoli

/-- The integer square cost equals the expression displayed in the paper. -/
theorem optimal_square_cost_formula (p : ℕ) (hp : 5 ≤ p) :
    (optimalSquareCost p hp : ℚ) =
      ((p - 1 : ℕ) : ℚ) * (1 - 1 / (optimalSquareOrder p hp : ℚ)) := by
  apply power_cycle_cost_formula
  exact (least_admissible_order_spec (p - 1) 2 (by decide) (by omega)).1.2.1

end Toffoli
