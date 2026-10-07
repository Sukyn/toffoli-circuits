import Toffoli.Foundations.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

namespace Toffoli

variable {K : Type*} [CommRing K] {n : ℕ}

/-- Gray words use false for + and true for -. -/
def polarizationSign (b : Bool) : K := if b then -1 else 1

/-- The part prepared on the first control by the chosen group circuits. -/
def polarizationSum (factors : Fin n → K) (word : Fin n → Bool) : K :=
  ∑ i, polarizationSign (word i) * factors i

/-- Fischer's coefficient before division by 2^n * (n+1)!. -/
def polarizationWeight (word : Fin n → Bool) : K :=
  ∏ i, polarizationSign (word i)

end Toffoli
