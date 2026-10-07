import Toffoli.Quadratic.QuadraticDiagonalization
import Toffoli.Quadratic.QuadraticDiagonalRank

namespace Toffoli

/-- The diagonalization gives one scaled square per nonzero diagonal entry.
The linear forms are rows of an invertible coordinate matrix, so none is
zero. Removing the zero diagonal entries leaves exactly `M.rank` terms. -/
theorem quadratic_square_decomposition {K : Type*} [Field K] {n : ℕ}
    (h2 : (2 : K) ≠ 0) (M : Matrix (Fin n) (Fin n) K) (hM : M.IsSymm) :
    ∃ terms : List (SquareTerm K n),
      (∀ term ∈ terms, term.Nonzero) ∧ terms.length = M.rank ∧
      (terms.map SquareTerm.matrix).sum = M := by
  classical
  obtain ⟨P, w, hP, hM⟩ := quadratic_diagonalization h2 M hM
  let indices := Finset.univ.filter (fun i => w i ≠ 0)
  let term (i : Fin n) : SquareTerm K n := ⟨w i, P i⟩
  refine ⟨indices.toList.map term, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
    have hiw : w i ≠ 0 := (Finset.mem_filter.mp (Finset.mem_toList.mp hi)).2
    refine ⟨hiw, ?_⟩
    intro hzero
    exact hP.ne_zero (Matrix.det_eq_zero_of_row_eq_zero i (fun j => congrFun hzero j))
  · simpa [indices] using (quadratic_diagonal_rank P w hP).symm.trans (congrArg Matrix.rank hM.symm)
  · rw [List.map_map, Finset.sum_map_toList, hM]
    ext i j
    rw [Matrix.sum_apply, Matrix.mul_apply]
    simp only [Function.comp_apply, SquareTerm.matrix, term,
      Matrix.mul_diagonal, Matrix.transpose_apply]
    dsimp only [indices]
    -- Zero diagonal entries contribute nothing, so all rows may be included.
    have hzero (a : Fin n) (ha : w a = 0) : w a * P a i * P a j = 0 := by
      simp [ha]
    rw [Finset.sum_filter_of_ne (fun a _ h => mt (hzero a) h)]
    exact Finset.sum_congr rfl (fun a _ => by ring)

end Toffoli
