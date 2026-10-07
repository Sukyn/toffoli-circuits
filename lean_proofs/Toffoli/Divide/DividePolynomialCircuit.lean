import Toffoli.Divide.DividePolynomialBound
import Toffoli.Divide.DivideProduct

namespace Toffoli

/-- The uniform Divide growth estimate is realized by a primitive circuit
on the original wires. Taking q=2 gives exponent log₂7; q=4 gives log₄23. -/
theorem divide_polynomial_circuit {p q d : ℕ} [Fact p.Prime]
    (hq : 2 ≤ q) (hp : q + 3 ≤ p) (hd : 1 ≤ d) (μ : ZMod p) :
    let W := 2 ^ q + 2 * q - 1
    ∃ c : MultiCircuit (ZMod p) d,
      c.Realizes (fun x => μ * ∏ i, x i) ∧
      (c.cost : ℝ) ≤ ((2 * 2 ^ q * W : ℕ) : ℝ) * (p : ℝ) *
        (d : ℝ) ^ Real.logb (q : ℝ) (W : ℝ) := by
  obtain ⟨c, hc, hcost⟩ := (divide_product (by omega : 5 ≤ p) hd μ).1
  refine ⟨c, hc, ?_⟩
  rw [hcost]
  exact divide_polynomial_bound hq hp hd

end Toffoli
