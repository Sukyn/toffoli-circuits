import Toffoli.Additions.PowerCycleModel
import Toffoli.Foundations.CoordinateLiftModel
import Toffoli.Foundations.InternalLiftModel
import Toffoli.Foundations.IndexedTargetModel

namespace Toffoli

/-- The power leaves may use any admissible affine return map. Membership
records its actual cycle-synthesis gates, without prescribing their cost. -/
def PowerCircuitFamily {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (μ : K) (d : ℕ) (c : Circuit K) : Prop :=
  ∃ (a b : K) (ha : a ≠ 0), PowerCycleAdmissible a b μ ha d ∧
    c = powerCycleCircuit a b μ ha d

/-- Place a power leaf on its source and destination wires. Internal targets
must differ from the source; all other wires retain their original positions. -/
inductive IndexedPowerCircuitFamily {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] {n : ℕ} (i : Fin n) :
    IndexedTarget n → K → ℕ → MultiCircuit K n → Prop
  | external {μ : K} {d : ℕ} {c : Circuit K}
      (member : PowerCircuitFamily μ d c) :
      IndexedPowerCircuitFamily i none μ d (c.lift i)
  | internal {μ : K} {d : ℕ} {c : Circuit K} (j : Fin n) (hij : i ≠ j)
      (member : PowerCircuitFamily μ d c) :
      IndexedPowerCircuitFamily i (some j) μ d (c.internalLift i j hij)

end Toffoli
