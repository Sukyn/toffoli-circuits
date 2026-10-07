import Toffoli.Quadratic.QuadraticModel
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.IsDiag

namespace Toffoli

open Module

/-- A symmetric matrix is congruent to a diagonal matrix, including when
it is singular. Mathlib constructs an orthogonal basis of the corresponding
bilinear form; the matrix of coordinates in that basis gives the congruence. -/
theorem quadratic_diagonalization {K : Type*} [Field K] {n : ℕ}
    (h2 : (2 : K) ≠ 0) (M : Matrix (Fin n) (Fin n) K) (hM : M.IsSymm) :
    ∃ (P : Matrix (Fin n) (Fin n) K) (w : Fin n → K),
      IsUnit P.det ∧ M = P.transpose * Matrix.diagonal w * P := by
  classical
  letI : Invertible (2 : K) := invertibleOfNonzero h2
  let B := Matrix.toBilin' M
  have hB : LinearMap.IsSymm B := by
    constructor
    intro x y
    change Matrix.toBilin' M x y = Matrix.toBilin' M y x
    simp only [Matrix.toBilin'_apply']
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM.eq, dotProduct_comm]
  obtain ⟨b, hb⟩ : ∃ b : Basis (Fin n) K (Fin n → K), B.IsOrthoᵢ b := by
    have hex := LinearMap.BilinForm.exists_orthogonal_basis hB
    rw [Module.finrank_fin_fun K] at hex
    exact hex
  let w := (B.toMatrix b).diag
  have hdiag : B.toMatrix b = Matrix.diagonal w := by
    have h : (B.toMatrix b).IsDiag := fun _ _ hij => by
      simpa only [LinearMap.BilinForm.toMatrix_apply] using hb hij
    exact h.diagonal_diag.symm
  let e := Pi.basisFun K (Fin n)
  refine ⟨b.toMatrix e, w, ?_, ?_⟩
  · exact Matrix.isUnit_det_of_left_inverse (e.toMatrix_mul_toMatrix_flip b)
  · rw [← hdiag, LinearMap.BilinForm.toMatrix_mul_basis_toMatrix]
    change M = LinearMap.BilinForm.toMatrix (Pi.basisFun K (Fin n)) (Matrix.toBilin' M)
    rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin']

end Toffoli
