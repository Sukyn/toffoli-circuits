import Mathlib.Data.List.Basic

namespace Toffoli

/-- Reversing a list of self-inverse updates undoes its final state. -/
theorem involutive_fold_reverse {α β : Type*} (step : β → α → β)
    (hinv : ∀ a, Function.Involutive (fun b => step b a)) (start : β) (steps : List α) :
    steps.reverse.foldl step (steps.foldl step start) = start := by
  induction steps generalizing start with
  | nil => rfl
  | cons a steps ih =>
    simp only [List.foldl_cons, List.reverse_cons, List.foldl_append, List.foldl_nil]
    rw [ih]
    exact hinv a start

end Toffoli
