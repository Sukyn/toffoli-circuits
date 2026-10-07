import Toffoli.Polynomial.PolynomialPowerModel
import Toffoli.Additions.LinearFormPowerAddition
import Toffoli.Foundations.MultiConstantAddition
import Toffoli.Foundations.MultiLinearAddition
import Mathlib.Algebra.Field.ZMod

namespace Toffoli

/-- Compile one term of the polynomial decomposition. Constants and linear
terms use the paper's affine construction with no transpositions. Higher
powers prepare the linear form, apply the cycle circuit, and unprepare it;
nonlinear powers of the zero form need no gates. -/
theorem polynomial_power_addition {p n : ℕ} [Fact p.Prime]
    (hn : 0 < n) (term : PolynomialPowerTerm (ZMod p) n)
    (hdegree : term.degree ≤ p - 2) :
    ∃ c : MultiCircuit (ZMod p) n, c.Realizes term.eval := by
  classical
  by_cases hzero : term.degree = 0
  · obtain ⟨c, hc, _⟩ := multi_constant_addition ⟨0, hn⟩ term.coefficient
    exact ⟨c, fun x t => by simpa [PolynomialPowerTerm.eval, hzero] using hc x t⟩
  by_cases hone : term.degree = 1
  · obtain ⟨c, hc, _⟩ := multi_linear_addition term.coefficient term.linear
    exact ⟨c, fun x t => by simpa [PolynomialPowerTerm.eval, hone] using hc x t⟩
  by_cases hlinear : ∃ i, term.linear i ≠ 0
  · apply linear_form_power_addition term.coefficient term.linear hlinear term.degree hzero
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using
      (show term.degree < p - 1 by omega)
  · push Not at hlinear
    exact ⟨[], by simp [MultiCircuit.Realizes, MultiCircuit.eval,
      PolynomialPowerTerm.eval, hlinear, zero_pow hzero]⟩

end Toffoli
