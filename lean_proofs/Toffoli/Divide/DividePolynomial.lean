import Toffoli.Divide.DividePolynomialBound

namespace Toffoli

/-- For every fixed polarization degree k, the polynomial-growth constant
is uniform in both p and the number of controls d. This numerical bound
does not require p to be prime. The exponent is exactly log base k-1 of
the paper's weighted number of recursive calls. -/
theorem divide_polynomial {k : ℕ} (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ p d : ℕ, k + 2 ≤ p → 1 ≤ d →
      (divideCount p d : ℝ) ≤ C * (p : ℝ) *
        (d : ℝ) ^ Real.logb ((k - 1 : ℕ) : ℝ)
          ((2 ^ (k - 1) + 2 * k - 3 : ℕ) : ℝ) := by
  let q := k - 1
  let W := 2 ^ q + 2 * q - 1
  have hq : 2 ≤ q := by dsimp [q]; omega
  have hpower : 1 ≤ (2 : ℕ) ^ q := Nat.one_le_two_pow
  have hW : 0 < W := by dsimp [W]; omega
  refine ⟨((2 * 2 ^ q * W : ℕ) : ℝ), by positivity, ?_⟩
  intro p d hp hd
  have hfield : q + 3 ≤ p := by dsimp [q]; omega
  have hweight : W = 2 ^ (k - 1) + 2 * k - 3 := by
    dsimp [W, q]
    omega
  have hbound := divide_polynomial_bound hq hfield hd
  change (divideCount p d : ℝ) ≤ ((2 * 2 ^ q * W : ℕ) : ℝ) * (p : ℝ) *
    (d : ℝ) ^ Real.logb (q : ℝ) (W : ℝ) at hbound
  simpa only [q, hweight] using hbound

end Toffoli
