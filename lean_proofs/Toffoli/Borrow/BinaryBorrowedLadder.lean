import Toffoli.Borrow.BorrowedLadder

namespace Toffoli

/-- `lem:binary-borrowed-ladder`: controls `a,b`, one control at each
middle stage, and `last` make every recorded update a Toffoli call.
The same execution restores all `d-2` dirty registers and its trace
contains exactly `4(d-2)` calls. The length counts gates directly. -/
theorem binaryBorrowedLadder_correct {K : Type*} [Ring K]
    (a b : K) (middle : List (K × K)) (last dirty t : K) :
    let controls := a :: b :: (middle.map Prod.fst ++ [last])
    let stages := middle.map (fun pair => BorrowedStage.mk pair.1 pair.2 1)
    runBorrowedLadder (a * b) stages last dirty t 1 1 =
      ⟨dirty, stages, t + controls.prod,
        borrowedCalls 1 (List.replicate middle.length 1) 1⟩ ∧
    1 + middle.length = controls.length - 2 ∧
    (runBorrowedLadder (a * b) stages last dirty t 1 1).calls.length =
      4 * (controls.length - 2) := by
  dsimp only
  obtain ⟨execution, _⟩ := borrowedLadder_correct (a * b)
    (middle.map (fun pair => BorrowedStage.mk pair.1 pair.2 1)) last dirty t 1 1
  -- These stages retain the original value pairs and assign cost one to each.
  simp [borrowedValues, borrowedCosts, List.map_map, Function.comp_def] at execution
  constructor
  · simpa [List.prod_append, mul_assoc] using execution
  constructor
  · simp only [List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega
  · rw [execution]
    simp [borrowedCalls]
    omega

end Toffoli
