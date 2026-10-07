import Toffoli.Foundations.MultiControlModel
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Toffoli

/-- Prepare the borrowed control, compare two target updates, and cancel
the preparation. The unknown initial borrowed value cancels as well. -/
def borrowProductSquareCircuit {K : Type*} [Field K] {n : ℕ}
    (prepare undo positive negative : MultiCircuit K n) : MultiCircuit K n :=
  prepare ++ positive ++ undo ++ negative

/-- The paper's Borrow wrapper. The three outer preparations move `y`
through `y + F`, `y - F`, and its original value; each inner block uses
a control from `F` as borrowed workspace for the current product `yH`. -/
def borrowProductCircuit {K : Type*} [Field K] {n : ℕ}
    (prepareF middleF prepareG undoG positive negative : MultiCircuit K n) :
    MultiCircuit K n :=
  prepareF ++ borrowProductSquareCircuit prepareG undoG positive negative ++
    middleF ++ borrowProductSquareCircuit prepareG undoG negative positive ++ prepareF

end Toffoli
