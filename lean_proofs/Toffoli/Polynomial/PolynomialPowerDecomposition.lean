import Toffoli.Polynomial.MonomialPowerDecomposition

namespace Toffoli

/-- Decompose each supported monomial by polarization and concatenate the
term lists. All powers retain their monomial degree, including degree zero
for constants and degree one for linear terms. This proves the algebraic
decomposition used by `thm:polynomial-synthesis`; circuit synthesis follows
by preparing and unpreparing each linear form. -/
theorem polynomial_power_decomposition {p k : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin k) (ZMod p)) (hdegree : f.totalDegree ≤ p - 2) :
    ∃ terms : List (PolynomialPowerTerm (ZMod p) k),
      (∀ term ∈ terms, term.degree ≤ p - 2) ∧
      ∀ x, MvPolynomial.eval x f = (terms.map (fun term => term.eval x)).sum := by
  classical
  choose pieces hbound heval using fun d : f.support =>
    monomial_power_decomposition d.val (f.coeff d.val)
      ((MvPolynomial.le_totalDegree d.property).trans hdegree)
  refine ⟨f.support.attach.toList.flatMap pieces, ?_, ?_⟩
  · intro term ht
    obtain ⟨d, _, ht⟩ := List.mem_flatMap.mp ht
    exact hbound d term ht
  · intro x
    simp only [List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map,
      Function.comp_def]
    simp_rw [← heval]
    rw [Finset.sum_map_toList, Finset.sum_attach f.support
      (fun d => MvPolynomial.eval x (MvPolynomial.monomial d (f.coeff d)))]
    -- Evaluation commutes with the supported monomial sum, which is f itself.
    rw [← MvPolynomial.eval_sum, MvPolynomial.support_sum_monomial_coeff]

end Toffoli
