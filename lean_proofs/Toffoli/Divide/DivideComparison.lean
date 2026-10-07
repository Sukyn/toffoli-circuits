import Toffoli.Divide.DivideDirectBound
import Toffoli.Divide.DivideStrictBound
import Toffoli.Additions.PowerCycleCostFormula

namespace Toffoli

/-- Divide-and-conquer never exceeds direct polarization in its degree
range, and is strictly cheaper from six controls onward. The right-hand
side is the paper's rational expression for the exact direct count. -/
theorem divide_comparison {p d : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hd : 2 ≤ d) (hdegree : d ≤ p - 2) :
    let r := leastAdmissibleOrder (p - 1) d (by omega) (by omega)
    (divideCount p d : ℚ) ≤
      (2 : ℚ) ^ (d - 1) * ((p - 1 : ℕ) : ℚ) * (1 - 1 / (r : ℚ)) ∧
    (6 ≤ d → (divideCount p d : ℚ) <
      (2 : ℚ) ^ (d - 1) * ((p - 1 : ℕ) : ℚ) * (1 - 1 / (r : ℚ))) := by
  dsimp only
  let r := leastAdmissibleOrder (p - 1) d (by omega) (by omega)
  have hdiv := (least_admissible_order_spec (p - 1) d (by omega) (by omega)).1.2.1
  have hformula : ((2 ^ (d - 1) * ((p - 1) - (p - 1) / r) : ℕ) : ℚ) =
      (2 : ℚ) ^ (d - 1) * ((p - 1 : ℕ) : ℚ) * (1 - 1 / (r : ℚ)) := by
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      power_cycle_cost_formula (p - 1) r hdiv, mul_assoc]
  rw [← hformula]
  constructor
  · exact_mod_cast divide_direct_bound hp hd hdegree
  · intro hlarge
    exact_mod_cast divide_strict_bound hp hlarge hdegree

end Toffoli
