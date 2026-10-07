import Toffoli.Borrow.BorrowProductModel
import Toffoli.Foundations.MultiCircuitCostAppend
import Toffoli.Foundations.MultiCircuitEvalAppend

namespace Toffoli

/-- A borrowed control turns two scaled Toffoli calls into an increment
`coefficient * x_y * product G`. The preparation never changes the factors
in `G`, so its inverse restores the borrowed value on every input. -/
theorem borrow_product_square {K : Type*} [Field K] {n : ℕ}
    (G : Finset (Fin n)) (y z : Fin n) (hyz : y ≠ z) (hz : z ∉ G)
    (coefficient : K) (prepare undo positive negative : MultiCircuit K n)
    (hprepare : ∀ x t, prepare.eval (x, t) =
      (Function.update x z (x z + ∏ j ∈ G, x j), t))
    (hundo : ∀ x t, undo.eval (x, t) =
      (Function.update x z (x z - ∏ j ∈ G, x j), t))
    (hpositive : positive.Realizes (fun x => coefficient * x y * x z))
    (hnegative : negative.Realizes (fun x => -coefficient * x y * x z)) :
    (borrowProductSquareCircuit prepare undo positive negative).Realizes
      (fun x => coefficient * x y * ∏ j ∈ G, x j) ∧
    (borrowProductSquareCircuit prepare undo positive negative).cost =
      prepare.cost + undo.cost + positive.cost + negative.cost := by
  unfold MultiCircuit.Realizes at hpositive hnegative
  constructor
  · intro x t
    simp only [borrowProductSquareCircuit, multi_circuit_eval_append, hprepare, hundo,
      hpositive, hnegative]
    apply Prod.ext
    -- The same product is added to and subtracted from the borrowed wire.
    · simp [Finset.prod_update_of_notMem hz]
    -- Subtracting the old target update cancels the unknown initial value of z.
    · simp [Finset.prod_update_of_notMem hz, hyz]
      ring
  · simp only [borrowProductSquareCircuit, multi_circuit_cost_append]
    ac_rfl

end Toffoli
