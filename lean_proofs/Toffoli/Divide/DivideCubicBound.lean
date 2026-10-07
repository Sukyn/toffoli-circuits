import Toffoli.Divide.DivideDirectBound
import Toffoli.Additions.CubicPowerCostBound

namespace Toffoli

/-- Direct cubic polarization uses four power additions. Since p is odd,
order two is admissible, and each addition costs at most half of p-1. -/
theorem divide_cubic_bound {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    divideCount p 3 ≤ 2 * (p - 1) := by
  exact (divide_direct_bound hp (by decide : 2 ≤ 3) (by omega)).trans
    (cubic_power_cost_bound hp)

end Toffoli
