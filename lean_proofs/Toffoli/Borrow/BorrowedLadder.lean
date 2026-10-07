import Toffoli.Borrow.BorrowedExecutionPass
import Toffoli.Borrow.BorrowedPropagation
import Toffoli.Borrow.BorrowedCalls

namespace Toffoli

/-- `lem:borrowed-ladder`: the same execution supplies the restored
state, product increment, exact call trace, and its transposition count.
Each call is one accumulator-form subcircuit assumed by the paper;
its inverse has the same supplied cost. Factors retain their order, so the
construction also works in a ring with noncommutative multiplication. -/
theorem borrowedLadder_correct {K : Type*} [Ring K]
    (first : K) (stages : List (BorrowedStage K)) (last dirty t : K)
    (qFirst qLast : ℕ) :
    runBorrowedLadder first stages last dirty t qFirst qLast =
      ⟨dirty, stages, t + first * ((borrowedValues stages).map Prod.fst).prod * last,
        borrowedCalls qFirst (borrowedCosts stages) qLast⟩ ∧
    ((runBorrowedLadder first stages last dirty t qFirst qLast).calls.map
      BorrowedCall.cost).sum =
      2 * qFirst + 4 * (borrowedCosts stages).sum + 2 * qLast := by
  have execution : runBorrowedLadder first stages last dirty t qFirst qLast =
      ⟨dirty, stages, t + first * ((borrowedValues stages).map Prod.fst).prod * last,
        borrowedCalls qFirst (borrowedCosts stages) qLast⟩ := by
    simp only [runBorrowedLadder, runBorrowedAdd, Bool.false_eq_true,
      if_false, if_true, runBorrowedPass_correct, add_neg_cancel_right]
    rw [borrowedPropagation_difference]
    simp only [borrowedCalls, List.cons_append, List.nil_append, List.append_assoc]
    congr 1
    -- Distribute over the last factor, then cancel the unprepared contribution.
    simp only [add_mul, add_assoc, add_neg_cancel_comm_assoc]
  constructor
  · exact execution
  · rw [execution]
    exact borrowedCalls_cost qFirst (borrowedCosts stages) qLast

end Toffoli
