import Toffoli.Mixed.MixedCircuitFamilyModel
import Toffoli.Foundations.AccumulatorLocalityModel

namespace Toffoli

/-- The compiler retains a derivation in the primitive family alongside
execution, exact cost, and locality. The family itself has no cost premise. -/
def FamilyProductConstruction (p : ℕ) [Fact p.Prime] (d b cost : ℕ) : Prop :=
  ∀ {n : ℕ} (controls pool : Finset (Fin n)), controls ⊆ pool →
    controls.card = d → pool.card = d + b →
    ∀ (target : IndexedTarget n), (∀ i ∈ pool, target ≠ some i) →
      ∀ μ : ZMod p, ∃ circuit : MultiCircuit (ZMod p) n,
        MixedCircuitFamily d b controls pool target μ circuit ∧
        (∀ x t, circuit.eval (x, t) =
          indexedTargetAdd target (μ * ∏ i ∈ controls, x i) (x, t)) ∧
        circuit.cost = cost ∧ circuit.AccumulatorLocal pool target

end Toffoli
