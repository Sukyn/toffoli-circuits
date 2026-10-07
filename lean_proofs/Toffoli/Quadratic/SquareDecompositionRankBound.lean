import Toffoli.Quadratic.QuadraticModel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

namespace Toffoli

/-- A list of r squares gives a matrix product with an inner dimension r.
Its rank is therefore at most r, including when some terms vanish or repeat. -/
theorem square_decomposition_rank_bound {K : Type*} [Field K] {n : ℕ}
    (terms : List (SquareTerm K n)) :
    ((terms.map SquareTerm.matrix).sum).rank ≤ terms.length := by
  let A : Matrix (Fin n) (Fin terms.length) K :=
    fun i j => (terms.get j).coefficient * (terms.get j).linear i
  let B : Matrix (Fin terms.length) (Fin n) K := fun j i => (terms.get j).linear i
  have hmatrix : (terms.map SquareTerm.matrix).sum = A * B := by
    conv_lhs => rw [← List.ofFn_get terms, List.map_ofFn, List.sum_ofFn]
    ext i j
    simp only [Matrix.mul_apply, Matrix.sum_apply, Function.comp_apply, SquareTerm.matrix, A, B]
  rw [hmatrix]
  exact (Matrix.rank_mul_le_left A B).trans (by simpa using Matrix.rank_le_card_width A)

end Toffoli
