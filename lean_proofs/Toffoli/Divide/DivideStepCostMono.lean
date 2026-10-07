import Toffoli.Divide.DivideModel

namespace Toffoli

/-- Replacing any child by a cheaper construction cannot increase a step's cost. -/
theorem divide_step_cost_mono (p : ℕ) {d : ℕ} (c : Composition (d - 1))
    (hdegree : c.length + 1 ≤ p - 2) (q r : Fin c.length → ℕ)
    (h : ∀ j, q j ≤ r j) :
    divideStepCost p c hdegree q ≤ divideStepCost p c hdegree r := by
  apply Nat.add_le_add_left
  exact Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left _ (h j))

end Toffoli
