import Toffoli.Foundations.IndexedTargetModel
import Toffoli.Borrow.BorrowedLadderModel
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Toffoli

/-- A grouped stage reads the product of its controls and the current value
of its dirty destination. The pair list follows the scalar ladder's order. -/
def indexedGroupedStageValues {K : Type*} [CommMonoid K] {n : ℕ}
    (stages : List (Finset (Fin n) × Fin n)) (x : Controls K n) : List (K × K) :=
  stages.map (fun stage => ((∏ i ∈ stage.1, x i), x stage.2))

end Toffoli
