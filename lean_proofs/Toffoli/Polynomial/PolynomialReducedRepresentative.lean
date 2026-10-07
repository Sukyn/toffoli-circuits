import Mathlib.FieldTheory.Finite.Polynomial

namespace Toffoli

universe u

/-- Every function on a finite field grid has a unique reduced polynomial.
Mathlib supplies existence through its evaluation map and uniqueness by
injectivity of evaluation on the subspace of reduced polynomials. -/
theorem polynomial_reduced_representative {K σ : Type u} [Field K] [Fintype K]
    [Finite σ] (g : (σ → K) → K) :
    ∃! f : MvPolynomial σ K,
      (∀ i, f.degreeOf i ≤ Fintype.card K - 1) ∧
      ∀ x, MvPolynomial.eval x f = g x := by
  classical
  have hbound (f : MvPolynomial σ K) :
      f ∈ MvPolynomial.restrictDegree σ K (Fintype.card K - 1) ↔
        ∀ i, f.degreeOf i ≤ Fintype.card K - 1 := by
    simpa only [MvPolynomial.degreeOf_def] using
      MvPolynomial.mem_restrictDegree_iff_sup σ f (Fintype.card K - 1)
  -- Evaluation is surjective on reduced polynomials, so choose the representative there.
  obtain ⟨f, heval⟩ := LinearMap.range_eq_top.mp (MvPolynomial.range_evalᵢ σ K) g
  refine ⟨f.val, ⟨(hbound f.val).mp f.property, fun x => congrFun heval x⟩, ?_⟩
  intro f' hf'
  -- Its injectivity gives uniqueness on the same reduced-polynomial subtype.
  suffices hsame : (⟨f', (hbound f').mpr hf'.1⟩ : MvPolynomial.R σ K) = f from
    congrArg Subtype.val hsame
  apply LinearMap.ker_eq_bot.mp (MvPolynomial.ker_evalₗ σ K)
  exact funext (fun x => (hf'.2 x).trans (congrFun heval x).symm)

end Toffoli
