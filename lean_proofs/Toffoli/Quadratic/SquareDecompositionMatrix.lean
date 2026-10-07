import Toffoli.Quadratic.QuadraticModel
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.Ring

namespace Toffoli
open scoped BigOperators

/-- Adding the outer-product matrices of square terms gives a symmetric
matrix whose quadratic function is exactly the sum of those squares. -/
theorem square_decomposition_matrix {K : Type*} [Field K] {n : ℕ}
    (terms : List (SquareTerm K n)) :
    ((terms.map SquareTerm.matrix).sum).IsSymm ∧
      ∀ x, quadraticValue ((terms.map SquareTerm.matrix).sum) x =
        (terms.map (fun term => term.eval x)).sum := by
  have hterm (term : SquareTerm K n) (x : Fin n → K) :
      quadraticValue term.matrix x = term.eval x := by
    simp only [quadraticValue, SquareTerm.matrix, SquareTerm.eval, pow_two,
      Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hadd (A B : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
      quadraticValue (A + B) x = quadraticValue A x + quadraticValue B x := by
    simp [quadraticValue, mul_add, add_mul, Finset.sum_add_distrib]
  induction terms with
  | nil =>
    constructor
    · rfl
    · intro x
      simp [quadraticValue]
  | cons term rest ih =>
    have hsymm : term.matrix.IsSymm := Matrix.IsSymm.ext fun i j => by
      simp [SquareTerm.matrix, mul_comm, mul_left_comm, mul_assoc]
    constructor
    · simpa only [List.map_cons, List.sum_cons] using hsymm.add ih.1
    · intro x
      simp only [List.map_cons, List.sum_cons]
      rw [hadd, hterm, ih.2]

end Toffoli
