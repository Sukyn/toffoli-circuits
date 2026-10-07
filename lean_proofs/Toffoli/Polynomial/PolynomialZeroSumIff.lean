import Toffoli.Polynomial.MultiControlZeroSumIff

namespace Toffoli

/-- The polynomial criterion: a reduced polynomial is realizable precisely
when the coefficient of the top monomial is zero. -/
theorem polynomial_zero_sum_iff {p n : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hn : 0 < n) (f : MvPolynomial (Fin n) (ZMod p))
    (hdegree : ∀ i, f.degreeOf i ≤ p - 1) :
    (∃ c : MultiCircuit (ZMod p) n, c.Realizes (fun x => MvPolynomial.eval x f)) ↔
      f.coeff (Finsupp.equivFunOnFinite.symm (fun _ : Fin n => p - 1)) = 0 := by
  rw [multi_control_zero_sum_iff hp hn]
  simpa only [ZMod.card] using polynomial_grid_zero_sum_iff f
    (by simpa only [ZMod.card] using hdegree)

end Toffoli
