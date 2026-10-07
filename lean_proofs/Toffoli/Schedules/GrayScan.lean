import Toffoli.Schedules.GrayScanCons
import Toffoli.Schedules.GrayFoldCons
import Toffoli.Schedules.GrayFlipInvolutive
import Toffoli.Schedules.InvolutiveScanReverse

namespace Toffoli

/-- Executing the flip-index list from all positive signs visits exactly the
reflected Gray list. Each successive signed sum therefore needs one update. -/
theorem gray_scan (n : ℕ) :
    (grayFlips n).scanl grayFlip (fun _ => false) = grayWords n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hfalse : Fin.cons false (fun _ : Fin n => false) = (fun _ => false) :=
      Fin.cons_self_tail (fun _ : Fin (n + 1) => false)
    change ((grayFlips n).map Fin.succ ++
      0 :: ((grayFlips n).map Fin.succ).reverse).scanl grayFlip (fun _ => false) =
      (grayWords n).map (Fin.cons false) ++ (grayWords n).reverse.map (Fin.cons true)
    rw [← hfalse, List.scanl_append, gray_scan_cons, gray_fold_cons, ih]
    simp only [List.scanl_cons, List.tail_cons]
    have hflip (word : GrayWord n) : grayFlip (Fin.cons false word) 0 = Fin.cons true word := by
      simp [grayFlip]
    rw [hflip, ← List.map_reverse, gray_scan_cons,
      involutive_scan_reverse grayFlip gray_flip_involutive, ih]

end Toffoli
