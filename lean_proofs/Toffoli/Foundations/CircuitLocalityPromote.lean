import Toffoli.Foundations.AccumulatorGatePromote

namespace Toffoli

/-- An internal preparation remains local when used as part of its parent.
Its control pool and target become parent controls, while the parent target
and every previously excluded wire remain protected at every gate. -/
theorem circuit_locality_promote {K : Type*} [Field K] {n : ℕ}
    (c : MultiCircuit K n) (childPool parentPool : Finset (Fin n))
    (hpool : childPool ⊆ parentPool) (childTarget : Fin n)
    (hchild : childTarget ∈ parentPool) (parentTarget : IndexedTarget n)
    (hparent : ∀ i ∈ parentPool, parentTarget ≠ some i)
    (hlocal : c.AccumulatorLocal childPool (some childTarget)) :
    c.AccumulatorLocal parentPool parentTarget := by
  refine ⟨hparent, ?_⟩
  intro gate hgate
  exact accumulator_gate_promote childPool parentPool hpool childTarget hchild
    parentTarget (hlocal.gates gate hgate)

end Toffoli
