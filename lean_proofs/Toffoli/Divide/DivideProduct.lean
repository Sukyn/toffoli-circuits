import Toffoli.Divide.IndexedDivideCost
import Toffoli.Divide.DivideRecurrence
import Toffoli.Divide.DivideCountOne
import Toffoli.Divide.DivideStepCostFormula

namespace Toffoli

/-- The recursive minimum is realized on the original d controls and one
target. The circuit restores every control and adds the scaled product.
Its cost is minimal within the recursive grouped-polarization family;
no claim is made about arbitrary circuits outside that family. -/
theorem divide_product {p d : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hd : 0 < d)
    (μ : ZMod p) :
    (∃ circuit : MultiCircuit (ZMod p) d,
      circuit.Realizes (fun x => μ * ∏ i, x i) ∧ circuit.cost = divideCount p d) ∧
      ∀ cost, DivideCost p d cost → divideCount p d ≤ cost := by
  obtain ⟨tree, hleast⟩ := divide_count_spec hp hd
  obtain ⟨circuit, hrun, hcost, _⟩ := indexed_divide_cost hp tree (Finset.univ : Finset (Fin d))
    (by simp) none (by simp) μ
  exact ⟨⟨circuit, by simpa only [indexedTargetAdd] using hrun, hcost⟩, hleast⟩

end Toffoli
