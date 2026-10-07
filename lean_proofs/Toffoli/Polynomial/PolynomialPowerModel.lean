import Mathlib.Algebra.MvPolynomial.Degrees

namespace Toffoli

/-- One scaled power of a linear form. Degree zero represents a constant. -/
structure PolynomialPowerTerm (K : Type*) (k : ℕ) where
  coefficient : K
  linear : Fin k → K
  degree : ℕ

def PolynomialPowerTerm.eval {K : Type*} [CommSemiring K] {k : ℕ}
    (term : PolynomialPowerTerm K k) (x : Fin k → K) : K :=
  term.coefficient * (∑ i, term.linear i * x i) ^ term.degree

end Toffoli
