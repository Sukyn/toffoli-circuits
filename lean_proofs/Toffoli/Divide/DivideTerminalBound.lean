import Toffoli.Divide.DivideDirectBound
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

namespace Toffoli

/-- A terminal problem of at most q controls costs at most 2^q*p:
SUM is free, and every direct power addition costs at most p. -/
theorem divide_terminal_bound {p q d : ℕ} (hp : 5 ≤ p) (hq : q ≤ p - 2)
    (hd : 1 ≤ d) (hdq : d ≤ q) : divideCount p d ≤ 2 ^ q * p := by
  by_cases hone : d = 1
  · simp [hone, divide_count_one]
  calc
    divideCount p d ≤ 2 ^ (d - 1) * ((p - 1) - (p - 1) /
        leastAdmissibleOrder (p - 1) d (by omega) (by omega)) :=
      divide_direct_bound hp (by omega) (hdq.trans hq)
    _ ≤ 2 ^ q * p := Nat.mul_le_mul
      (pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (by omega))
      ((Nat.sub_le _ _).trans (Nat.sub_le p 1))

end Toffoli
