import Toffoli.Mixed.MixedFamilyMinimum
import Mathlib.Data.Fin.Embedding

namespace Toffoli

/-- The paper's exact recurrence, on `d` controls, `b` dirty wires and one
target. Embed the controls in the first `d` positions of the available pool;
the general family theorem supplies the circuit and its minimality. -/
theorem borrowed_recursion {p d : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hd : 0 < d) (b : ℕ) :
    ∃ (controls : Finset (Fin (d + b))) (circuit : MultiCircuit (ZMod p) (d + b)),
      controls.card = d ∧
      MixedCircuitFamily d b controls Finset.univ none 1 circuit ∧
      circuit.Realizes (fun x => ∏ i ∈ controls, x i) ∧
      circuit.cost = mixedCount p hp d b ∧
      circuit.AccumulatorLocal Finset.univ none ∧
      circuit.cost ≤ min (divideCount p d) (borrowCost (2 * optimalSquareCost p hp) d) ∧
      ∀ other : MultiCircuit (ZMod p) (d + b),
        MixedCircuitFamily d b controls Finset.univ none 1 other →
        circuit.cost ≤ other.cost := by
  let controls := (Finset.univ : Finset (Fin d)).map (Fin.castAddEmb b)
  have hcontrols : controls.card = d := by simp [controls]
  obtain ⟨circuit, member, hrun, hcost, hlocal, hbound, hminimum⟩ :=
    mixed_family_minimum (b := b) hp hd controls Finset.univ (Finset.subset_univ _)
      hcontrols (by simp) none (by simp) 1 one_ne_zero
  exact ⟨controls, circuit, hcontrols, member,
    by simpa only [indexedTargetAdd, one_mul] using hrun,
    hcost, hlocal, hbound, hminimum⟩

end Toffoli
