import Toffoli.Divide.DivideModel
import Toffoli.Additions.PowerCycleCostFormula

namespace Toffoli

/-- The integer cost of one recursive step is the rational expression in
the paper. The power order divides p-1, so its quotient is exact. -/
theorem divide_step_cost_formula (p : ℕ) {d : ℕ} (c : Composition (d - 1))
    (hdegree : c.length + 1 ≤ p - 2) (q : Fin c.length → ℕ) :
    (divideStepCost p c hdegree q : ℚ) =
      (2 : ℚ) ^ c.length * ((p - 1 : ℕ) : ℚ) *
        (1 - 1 / (leastAdmissibleOrder (p - 1) (c.length + 1)
          (by omega) (by omega) : ℚ)) +
        ∑ j : Fin c.length, ((2 + 2 ^ j.val : ℕ) : ℚ) * (q j : ℚ) := by
  have hdiv :=
    (least_admissible_order_spec (p - 1) (c.length + 1) (by omega) (by omega)).1.2.1
  have hpower := power_cycle_cost_formula (p - 1) _ hdiv
  simp only [divideStepCost, Nat.cast_add, Nat.cast_sum, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat, hpower, mul_assoc]

end Toffoli
