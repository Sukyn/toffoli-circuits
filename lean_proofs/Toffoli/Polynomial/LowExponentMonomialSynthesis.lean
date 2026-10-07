import Toffoli.Polynomial.ZeroSumFactorProduct
import Toffoli.Divide.DivideProduct
import Toffoli.Additions.FiniteFieldPowerSum

namespace Toffoli

/-- A monomial is constructible when each exponent is at most `p - 2`,
with no bound on their sum. Start with the product circuit and replace its
linear factors by powers, whose unary sums vanish. For example, this gives
`x₀³*x₁³` over `ZMod 5`, beyond the total-degree range of polarization. -/
theorem low_exponent_monomial_synthesis {p n : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hn : 0 < n) (d : Fin n → ℕ) (hd : ∀ i, d i ≤ p - 2)
    (μ : ZMod p) :
    ∃ c : MultiCircuit (ZMod p) n,
      c.Realizes (fun x => μ * ∏ i, x i ^ d i) := by
  apply zero_sum_factor_product (f := fun i a => a ^ d i) ?_ ?_ μ
  · intro coefficient
    obtain ⟨c, hrun, _⟩ := (divide_product hp hn coefficient).1
    exact ⟨c, hrun⟩
  · intro i
    apply FiniteField.sum_pow_lt_card_sub_one
    rw [ZMod.card]
    have := hd i
    omega

end Toffoli
