import Toffoli.Polynomial.PolynomialGridSum

namespace Toffoli

/-- A reduced polynomial has zero sum over the field grid exactly when
its highest possible monomial has coefficient zero. The factor `(-1)^k`
in the grid formula is always nonzero, including in characteristic two. -/
theorem polynomial_grid_zero_sum_iff {K σ : Type*} [Field K] [Fintype K]
    [Fintype σ] [DecidableEq σ] (f : MvPolynomial σ K)
    (hdegree : ∀ i, f.degreeOf i ≤ Fintype.card K - 1) :
    (∑ x : σ → K, MvPolynomial.eval x f) = 0 ↔
      f.coeff (Finsupp.equivFunOnFinite.symm (fun _ : σ => Fintype.card K - 1)) = 0 := by
  rw [polynomial_grid_sum f hdegree]
  simp

end Toffoli
