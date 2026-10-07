import Toffoli.Quadratic.QuadraticModel

namespace Toffoli

/-- Congruence by an invertible matrix preserves rank. A diagonal matrix
has one rank contribution for each nonzero diagonal coefficient. -/
theorem quadratic_diagonal_rank {K : Type*} [Field K] [DecidableEq K] {n : ℕ}
    (P : Matrix (Fin n) (Fin n) K) (w : Fin n → K) (hP : IsUnit P.det) :
    (P.transpose * Matrix.diagonal w * P).rank =
      (Finset.univ.filter (fun i => w i ≠ 0)).card := by
  rw [Matrix.rank_mul_eq_left_of_isUnit_det P _ hP,
    Matrix.rank_mul_eq_right_of_isUnit_det P.transpose _ (Matrix.isUnit_det_transpose P hP),
    Matrix.rank_diagonal, Fintype.card_subtype]

end Toffoli
