import Toffoli.Divide.DivideTripleGrouping
import Toffoli.Divide.DivideCubicBound
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Tactic.Ring

namespace Toffoli

/-- A triple group saves enough power calls to pay for its three
preparations. Once d is at least six, the saving is strictly positive. -/
theorem divide_strict_bound {p d : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hd : 6 ≤ d) (hdegree : d ≤ p - 2) :
    divideCount p d < 2 ^ (d - 1) * ((p - 1) - (p - 1) /
      leastAdmissibleOrder (p - 1) d (by omega) (by omega)) := by
  let r := leastAdmissibleOrder (p - 1) d (by omega) (by omega)
  have horder : 0 < r ∧ r ∣ p - 1 ∧ ¬r ∣ d :=
    (least_admissible_order_spec (p - 1) d (by omega) (by omega)).1
  have hr : 2 ≤ r := by
    exact (Nat.two_le_iff r).2
      ⟨Nat.ne_of_gt horder.1, fun h => horder.2.2 (by simp [h])⟩

  -- Every admissible order is at least two, so a power costs at least half of p-1.
  have hhalf : p - 1 ≤ 2 * ((p - 1) - (p - 1) / r) := by
    have hquotient := Nat.div_le_div_left (a := p - 1) hr (by decide : 0 < 2)
    omega

  -- There are at least eight power calls, but only six preparation units.
  have hlarge : 8 ≤ (2 : ℕ) ^ (d - 3) :=
    pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (by omega : 3 ≤ d - 3)
  calc
    divideCount p d ≤ 2 ^ (d - 3) * (p - 1) + 3 * (2 * (p - 1)) :=
      (divide_triple_grouping hp (by omega) hdegree).trans
        (add_le_add (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
          (Nat.mul_le_mul_left 3 (divide_cubic_bound hp)))
    _ = (2 ^ (d - 3) + 6) * (p - 1) := by ring
    _ < 2 ^ (d - 2) * (p - 1) := by
      rw [show d - 2 = (d - 3) + 1 by omega, pow_succ]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    _ ≤ 2 ^ (d - 2) * (2 * ((p - 1) - (p - 1) / r)) :=
      Nat.mul_le_mul_left _ hhalf
    _ = 2 ^ (d - 1) * ((p - 1) - (p - 1) / r) := by
      rw [show d - 1 = (d - 2) + 1 by omega, pow_succ]
      ring

end Toffoli
