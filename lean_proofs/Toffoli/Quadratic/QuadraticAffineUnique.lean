import Toffoli.Quadratic.QuadraticModel
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.LinearCombination

namespace Toffoli

/-- Changing the affine part cannot change a symmetric quadratic matrix when
two is nonzero. Subtract the values at x and y from the value at x+y, then
add the value at zero: every affine term cancels. On coordinate unit vectors,
the remaining expression is twice the corresponding matrix entry. -/
theorem quadratic_affine_unique {K : Type*} [Field K] {n : ℕ}
    (h2 : (2 : K) ≠ 0) (M N : Matrix (Fin n) (Fin n) K)
    (hM : M.IsSymm) (hN : N.IsSymm) (b c : K) (a d : Fin n → K)
    (heval : ∀ x, quadraticValue M x + affineValue b a x =
      quadraticValue N x + affineValue c d x) : M = N := by
  have hconstant : b = c := by
    simpa [quadraticValue, affineValue] using heval 0
  have hpolar (A : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
      quadraticValue A (x + y) - quadraticValue A x - quadraticValue A y =
        Matrix.toBilin' A x y + Matrix.toBilin' A y x := by
    simpa only [QuadraticMap.polar, LinearMap.BilinMap.toQuadraticMap_apply,
      quadraticValue, Matrix.toBilin'_apply] using
      LinearMap.BilinMap.polar_toQuadraticMap (B := Matrix.toBilin' A) x y
  have hsecond (x y : Fin n → K) :
      quadraticValue M (x + y) - quadraticValue M x - quadraticValue M y =
        quadraticValue N (x + y) - quadraticValue N x - quadraticValue N y := by
    have hx := heval x
    have hy := heval y
    have hxy := heval (x + y)
    simp only [affineValue, Pi.add_apply, mul_add, Finset.sum_add_distrib] at hx hy hxy
    linear_combination hxy - hx - hy + hconstant
  ext i j
  have h := hsecond (Pi.single i 1) (Pi.single j 1)
  rw [hpolar, hpolar] at h
  apply mul_left_cancel₀ h2
  simpa only [Matrix.toBilin'_single, hM.apply i j, hN.apply i j, ← two_mul] using h

end Toffoli
