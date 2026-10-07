import Toffoli.Polynomial.MultiControlZeroSumIff
import Toffoli.Polynomial.PolynomialLowDegreeSum

namespace Toffoli

/-- Total degree below `n * (p - 1)` forces zero grid sum, hence gives an
accumulator circuit. The polynomial need not first be reduced. -/
theorem polynomial_low_degree_synthesis {p n : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hn : 0 < n) (f : MvPolynomial (Fin n) (ZMod p))
    (hdegree : f.totalDegree < n * (p - 1)) :
    ∃ c : MultiCircuit (ZMod p) n, c.Realizes (fun x => MvPolynomial.eval x f) := by
  apply (multi_control_zero_sum_iff hp hn _).mpr
  exact polynomial_low_degree_sum f
    (by simpa only [Fintype.card_fin, ZMod.card] using hdegree)

end Toffoli
