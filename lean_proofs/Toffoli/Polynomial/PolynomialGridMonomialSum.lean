import Toffoli.Additions.FiniteFieldPowerSum
import Mathlib.Algebra.MvPolynomial.Eval

namespace Toffoli

/-- Summation over a product grid factors into one sum for each variable.
For reduced monomials, every factor vanishes unless every exponent is
`card K - 1`; the surviving product is one factor of `-1` per variable. -/
theorem polynomial_grid_monomial_sum {K σ : Type*} [Field K] [Fintype K]
    [Fintype σ] [DecidableEq σ] (d : σ →₀ ℕ)
    (hd : ∀ i, d i ≤ Fintype.card K - 1) :
    ∑ x : σ → K, ∏ i, x i ^ d i =
      if d = Finsupp.equivFunOnFinite.symm (fun _ : σ => Fintype.card K - 1)
      then (-1 : K) ^ Fintype.card σ else 0 := by
  classical
  rw [← Fintype.prod_sum (fun i (x : K) => x ^ d i)]
  simp_rw [finite_field_power_sum _ (hd _)]
  split_ifs with htop
  · simp [htop]
  · obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp htop
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg (by simpa using hi))

end Toffoli
