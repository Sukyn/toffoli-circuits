import Toffoli.Borrow.BorrowedExecutionModel

namespace Toffoli

/-- The state and trace are projections of the same recursive execution. -/
theorem runBorrowedPass_correct {K : Type*} [Ring K] (b : K)
    (stages : List (BorrowedStage K)) (last t : K) (qLast : ℕ) (inverse : Bool) :
    runBorrowedPass b stages last t qLast inverse =
      ⟨b, stages,
        t + if inverse then -(borrowedPropagation b (borrowedValues stages) * last)
          else borrowedPropagation b (borrowedValues stages) * last,
        (borrowedCosts stages).map (fun q => BorrowedCall.middle q false) ++
          [.target qLast inverse] ++
          (borrowedCosts stages).reverse.map (fun q => BorrowedCall.middle q true)⟩ := by
  induction stages generalizing b with
  | nil => cases inverse <;> simp [runBorrowedPass, runBorrowedAdd,
      borrowedPropagation, borrowedValues, borrowedCosts]
  | cons stage rest ih =>
    simp [runBorrowedPass, runBorrowedAdd, ih, borrowedPropagation, borrowedValues,
      borrowedCosts, List.map_append, List.append_assoc]

end Toffoli
