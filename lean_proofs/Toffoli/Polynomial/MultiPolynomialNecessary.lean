import Toffoli.Polynomial.MultiControlZeroSumNecessary
import Toffoli.Polynomial.PolynomialGridZeroSum

namespace Toffoli

/-- The necessary coefficient condition for any number of controls.
The polynomial is the reduced representative; its grid sum is a nonzero
multiple of its top coefficient, and every accumulator circuit has sum zero.
The converse is proved by algebraic synthesis in `PolynomialZeroSumIff`. -/
theorem multi_polynomial_coefficient_necessary {K : Type*} [Field K] [Fintype K]
    (hcard : 2 < Fintype.card K) {n : ℕ} (f : MvPolynomial (Fin n) K)
    (hdegree : ∀ i, f.degreeOf i ≤ Fintype.card K - 1)
    (c : MultiCircuit K n) (hc : c.Realizes (fun x => MvPolynomial.eval x f)) :
    f.coeff (Finsupp.equivFunOnFinite.symm (fun _ : Fin n => Fintype.card K - 1)) = 0 := by
  exact (polynomial_grid_zero_sum_iff f hdegree).mp
    (multi_control_zero_sum_necessary hcard c _ hc)

end Toffoli
