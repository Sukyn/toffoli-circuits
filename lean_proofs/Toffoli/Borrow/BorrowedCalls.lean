import Toffoli.Borrow.BorrowedLadderModel

namespace Toffoli

/-- Counts the calls actually listed by `borrowedCalls`, including both undo passes. -/
theorem borrowedCalls_cost (first : ℕ) (middle : List ℕ) (last : ℕ) :
    ((borrowedCalls first middle last).map BorrowedCall.cost).sum =
      2 * first + 4 * middle.sum + 2 * last := by
  simp [borrowedCalls, BorrowedCall.cost, List.map_map, Function.comp_def]
  omega

end Toffoli
