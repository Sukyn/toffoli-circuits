import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring

/-! A grouped ladder at the level of the accumulator subcircuits assumed
by the paper. A middle register is `(factor, initial borrowed value)`.
The factors are read-only controls. The recursive pass explicitly prepares
a borrowed register, runs the remaining pass, then subtracts its preparation.
-/
namespace Toffoli

variable {K : Type*} [Semiring K]

def borrowedPropagation (b : K) : List (K × K) → K
  | [] => b
  | (factor, dirty) :: rest => borrowedPropagation (dirty + b * factor) rest

/-- The Boolean records an inverse/subtracting call. -/
inductive BorrowedCall where
  | first (cost : ℕ) (inverse : Bool)
  | middle (cost : ℕ) (inverse : Bool)
  | target (cost : ℕ) (inverse : Bool)

def BorrowedCall.cost : BorrowedCall → ℕ
  | .first q _ | .middle q _ | .target q _ => q

def borrowedCalls (first : ℕ) (middle : List ℕ) (last : ℕ) : List BorrowedCall :=
  let prepare := middle.map (fun q => BorrowedCall.middle q false)
  let undo := middle.reverse.map (fun q => BorrowedCall.middle q true)
  [.first first false] ++ prepare ++ [.target last false] ++ undo ++
    [.first first true] ++ prepare ++ [.target last true] ++ undo

end Toffoli
