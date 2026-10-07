import Toffoli.Quadratic.SquareDecompositionRankBound
import Toffoli.Quadratic.SquareDecompositionMatrix
import Toffoli.Quadratic.QuadraticAffineUnique

namespace Toffoli

/-- Every representation of a symmetric quadratic function as scaled squares
uses at least the matrix rank many terms. Competitors may use a different
affine part, zero terms, repeated linear forms, or arbitrary coefficients. -/
theorem square_decomposition_lower_bound {K : Type*} [Field K] {n : ℕ}
    (h2 : (2 : K) ≠ 0) (M : Matrix (Fin n) (Fin n) K) (hM : M.IsSymm)
    (b : K) (a : Fin n → K) (terms : List (SquareTerm K n))
    (c : K) (d : Fin n → K)
    (heval : ∀ x, quadraticValue M x + affineValue b a x =
      (terms.map (fun term => term.eval x)).sum + affineValue c d x) :
    M.rank ≤ terms.length := by
  obtain ⟨hsymm, hvalue⟩ := square_decomposition_matrix terms
  have hmatrix := quadratic_affine_unique h2 M (terms.map SquareTerm.matrix).sum
    hM hsymm b c a d (fun x => (heval x).trans (by rw [hvalue]))
  rw [hmatrix]
  exact square_decomposition_rank_bound terms

end Toffoli
