import Mathlib.FieldTheory.ChevalleyWarning

namespace Toffoli

/-- The low-total-degree consequence in `prop:polynomial-zero-sum` follows
directly from Mathlib's finite-field summation theorem. No preliminary
reduction of the polynomial is needed for this algebraic conclusion. -/
theorem polynomial_low_degree_sum {K σ : Type*} [Field K] [Fintype K]
    [Fintype σ] [DecidableEq σ] (f : MvPolynomial σ K)
    (hdegree : f.totalDegree < Fintype.card σ * (Fintype.card K - 1)) :
    ∑ x : σ → K, MvPolynomial.eval x f = 0 := by
  exact MvPolynomial.sum_eval_eq_zero f (by simpa [Nat.mul_comm] using hdegree)

end Toffoli
