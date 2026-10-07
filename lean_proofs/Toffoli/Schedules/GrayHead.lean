import Toffoli.Schedules.GrayModel

namespace Toffoli

/-- The traversal begins with every group added positively. -/
theorem gray_head (n : ℕ) : (grayWords n).head? = some (fun _ => false) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : Fin.cons false (fun _ : Fin n => false) = (fun _ => false) :=
      Fin.cons_self_tail (fun _ : Fin (n + 1) => false)
    simp [grayWords, ih, h]

end Toffoli
