import Toffoli.Additions.AdmissibleOrder
import Mathlib.LinearAlgebra.Matrix.Rank

namespace Toffoli

/-- One scaled square of a linear form, as in the polynomial appendix. -/
structure SquareTerm (K : Type*) (n : ℕ) where
  coefficient : K
  linear : Fin n → K

variable {K : Type*} [Field K] {n : ℕ}

def SquareTerm.matrix (term : SquareTerm K n) : Matrix (Fin n) (Fin n) K :=
  fun i j => term.coefficient * term.linear i * term.linear j

def SquareTerm.eval (term : SquareTerm K n) (x : Fin n → K) : K :=
  term.coefficient * (∑ i, term.linear i * x i) ^ 2

def SquareTerm.Nonzero (term : SquareTerm K n) : Prop :=
  term.coefficient ≠ 0 ∧ term.linear ≠ 0

def quadraticValue (M : Matrix (Fin n) (Fin n) K) (x : Fin n → K) : K :=
  ∑ i, ∑ j, x i * M i j * x j

def affineValue (constant : K) (linear : Fin n → K) (x : Fin n → K) : K :=
  constant + ∑ i, linear i * x i

/-- The same least admissible order used for one-control square additions. -/
def optimalSquareOrder (p : ℕ) (hp : 5 ≤ p) : ℕ :=
  leastAdmissibleOrder (p - 1) 2 (by decide) (by omega)

def optimalSquareCost (p : ℕ) (hp : 5 ≤ p) : ℕ :=
  (p - 1) - (p - 1) / optimalSquareOrder p hp

end Toffoli
