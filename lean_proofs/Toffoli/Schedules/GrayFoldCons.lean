import Toffoli.Schedules.GrayFlipCons

namespace Toffoli

/-- Shifted flip indices leave the newly prefixed sign unchanged. -/
theorem gray_fold_cons {n : ℕ} (b : Bool) (word : GrayWord n) (flips : List (Fin n)) :
    (flips.map Fin.succ).foldl grayFlip (Fin.cons b word) =
      Fin.cons b (flips.foldl grayFlip word) := by
  rw [List.foldl_map]
  exact List.foldl_hom (Fin.cons (n := n) (α := fun _ => Bool) b) (gray_flip_cons (n := n) b)

end Toffoli
