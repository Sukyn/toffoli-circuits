import Toffoli.Polynomial.PolynomialGridMonomialSum
import Mathlib.Algebra.MvPolynomial.Degrees

namespace Toffoli

/-- The coefficient formula used in `prop:polynomial-zero-sum`.
Expand the evaluations into monomials and sum each monomial over the grid.
Only the monomial with exponent `card K - 1` in every variable survives.
This is an algebraic identity; circuit existence is a separate question. -/
theorem polynomial_grid_sum {K σ : Type*} [Field K] [Fintype K]
    [Fintype σ] [DecidableEq σ] (f : MvPolynomial σ K)
    (hdegree : ∀ i, f.degreeOf i ≤ Fintype.card K - 1) :
    ∑ x : σ → K, MvPolynomial.eval x f =
      (-1 : K) ^ Fintype.card σ *
        f.coeff (Finsupp.equivFunOnFinite.symm (fun _ : σ => Fintype.card K - 1)) := by
  classical
  simp_rw [MvPolynomial.eval_eq']
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_eq_single
    (Finsupp.equivFunOnFinite.symm (fun _ : σ => Fintype.card K - 1))]
  · rw [polynomial_grid_monomial_sum _ (by simp)]
    simp [mul_comm]
  · intro d hd hne
    rw [polynomial_grid_monomial_sum d
      (fun i => (MvPolynomial.monomial_le_degreeOf i hd).trans (hdegree i)),
      if_neg hne, mul_zero]
  · intro hnot
    simp [MvPolynomial.notMem_support_iff.mp hnot]

end Toffoli
