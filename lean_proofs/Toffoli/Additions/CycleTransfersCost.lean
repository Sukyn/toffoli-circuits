import Toffoli.Additions.CycleTransfers
import Toffoli.Foundations.CircuitCostAppend

namespace Toffoli

/-- Each remaining cycle label contributes exactly one transposition. -/
theorem cycleTransfers_cost {K : Type*} [Field K] [DecidableEq K]
    (a : K) (labels : List K) (f : K → K) :
    (cycleTransfers a labels f).cost = labels.length := by
  induction labels generalizing f with
  | nil => rfl
  | cons b rest ih =>
    rw [cycleTransfers, circuit_cost_append, ih]
    change 1 + rest.length = rest.length + 1
    omega

end Toffoli
