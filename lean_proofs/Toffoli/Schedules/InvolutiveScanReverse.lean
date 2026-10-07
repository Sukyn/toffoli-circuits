import Toffoli.Schedules.InvolutiveFoldReverse

namespace Toffoli

/-- The reverse execution visits the same states in reverse order. -/
theorem involutive_scan_reverse {α β : Type*} (step : β → α → β)
    (hinv : ∀ a, Function.Involutive (fun b => step b a)) (start : β) (steps : List α) :
    steps.reverse.scanl step (steps.foldl step start) = (steps.scanl step start).reverse := by
  induction steps generalizing start with
  | nil => simp
  | cons a steps ih =>
    simp only [List.foldl_cons, List.reverse_cons, List.scanl_append, List.scanl_cons,
      List.scanl_nil, List.tail_cons]
    rw [ih, involutive_fold_reverse step hinv]
    simp [hinv a start]

end Toffoli
