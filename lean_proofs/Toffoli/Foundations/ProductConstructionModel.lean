import Toffoli.Foundations.AccumulatorLocalityModel

namespace Toffoli

/-- A product-addition compiler with `d` controls and `b` available borrowed
wires. The pool contains both sets; the target is excluded. One circuit
witness supplies execution, exact cost, and gatewise locality together.
Quantifying over wire indices lets a parent use the compiler on any subpool. -/
def ProductConstruction (K : Type*) [Field K] (d b cost : ℕ) : Prop :=
  ∀ {n : ℕ} (controls pool : Finset (Fin n)), controls ⊆ pool →
    controls.card = d → pool.card = d + b →
    ∀ (target : IndexedTarget n), (∀ i ∈ pool, target ≠ some i) →
      ∀ μ : K, ∃ circuit : MultiCircuit K n,
        (∀ x t, circuit.eval (x, t) =
          indexedTargetAdd target (μ * ∏ i ∈ controls, x i) (x, t)) ∧
        circuit.cost = cost ∧ circuit.AccumulatorLocal pool target

end Toffoli
