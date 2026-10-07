import Toffoli.Polynomial.MonomialPowerFactors
import Mathlib.Data.Finsupp.Multiset

namespace Toffoli

/-- An exponent vector becomes a list of variable occurrences. For example,
`c₁²*c₂` gives `[c₁,c₁,c₂]`, to which the same polarization identity applies.
The resulting powers all have the original monomial's total degree. -/
theorem monomial_power_decomposition {p k : ℕ} [Fact p.Prime]
    (d : Fin k →₀ ℕ) (μ : ZMod p) (hd : (d.sum fun _ e => e) ≤ p - 2) :
    ∃ terms : List (PolynomialPowerTerm (ZMod p) k),
      (∀ term ∈ terms, term.degree ≤ p - 2) ∧
      ∀ x, MvPolynomial.eval x (MvPolynomial.monomial d μ) =
        (terms.map (fun term => term.eval x)).sum := by
  classical
  let labels := d.toMultiset.toList
  have hlength : labels.length = d.sum (fun _ e => e) := by
    simp [labels, Function.id_def]
  obtain ⟨terms, hdegree, heval⟩ := monomial_power_factors
    (by simpa only [hlength] using hd) μ (fun j : Fin labels.length => labels[j.1])
  refine ⟨terms, fun term ht => (hdegree term ht).trans_le (hlength.trans_le hd), ?_⟩
  intro x
  have hprod : (∏ j : Fin labels.length, x labels[j.1]) =
      d.prod (fun i e => x i ^ e) := by
    rw [Fin.prod_univ_fun_getElem]
    change (d.toMultiset.toList.map x).prod = _
    rw [Multiset.prod_map_toList, Finset.prod_multiset_map_count]
    simp [Finsupp.prod]
  simpa only [MvPolynomial.eval_monomial, hprod] using heval x

end Toffoli
