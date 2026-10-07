import Toffoli.Divide.DivideDepthBound
import Toffoli.Divide.GeometricSumBound
import Toffoli.Divide.NaturalPowerLogBound
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Toffoli
open scoped BigOperators

/-- A fixed q-way grouping has a polynomial bound with a constant depending
only on q. The extra factor W pays for rounding the recursion depth upward. -/
theorem divide_polynomial_bound {p q d : ℕ} (hq : 2 ≤ q) (hp : q + 3 ≤ p)
    (hd : 1 ≤ d) :
    let W := 2 ^ q + 2 * q - 1
    (divideCount p d : ℝ) ≤ ((2 * 2 ^ q * W : ℕ) : ℝ) * (p : ℝ) *
      (d : ℝ) ^ Real.logb (q : ℝ) (W : ℝ) := by
  let W := 2 ^ q + 2 * q - 1
  let h := Nat.log q d + 1
  have hpower : 1 ≤ (2 : ℕ) ^ q := Nat.one_le_two_pow
  have hW : 2 ≤ W := by dsimp [W]; omega
  have hdepth : d ≤ q ^ h :=
    (Nat.lt_pow_succ_log_self (show 1 < q by omega) d).le
  have hlevels : ∑ i ∈ Finset.range (h + 1), W ^ i ≤ 2 * W ^ h :=
    (Nat.le_add_right _ 1).trans (geometric_sum_bound hW h)
  have hcount : divideCount p d ≤ 2 ^ q * p * (2 * W ^ h) :=
    (divide_depth_bound hq hp hd hdepth).trans
      (Nat.mul_le_mul_left (2 ^ q * p) hlevels)

  -- Round the depth up by one, then express the preceding level as a real power.
  have hlast := natural_power_log_bound hq (show 1 ≤ W by omega) hd
  calc
    (divideCount p d : ℝ) ≤ ((2 ^ q * p * (2 * W ^ h) : ℕ) : ℝ) := by
      exact_mod_cast hcount
    _ = ((2 * 2 ^ q * W : ℕ) : ℝ) * (p : ℝ) *
        ((W ^ Nat.log q d : ℕ) : ℝ) := by
      simp only [h, pow_succ, Nat.cast_mul]
      ring
    _ ≤ ((2 * 2 ^ q * W : ℕ) : ℝ) * (p : ℝ) *
        (d : ℝ) ^ Real.logb (q : ℝ) (W : ℝ) :=
      mul_le_mul_of_nonneg_left hlast (by positivity)

end Toffoli
