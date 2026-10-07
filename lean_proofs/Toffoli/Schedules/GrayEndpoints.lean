import Toffoli.Schedules.GrayHead

namespace Toffoli

/-- Only the first group has a negative sign at the end. Thus restoration
calls that group positively and every remaining group negatively. -/
theorem gray_endpoints (n : ℕ) :
    (grayWords (n + 1)).head? = some (fun _ => false) ∧
    (grayWords (n + 1)).getLast? = some (Fin.cons true (fun _ : Fin n => false)) := by
  refine ⟨gray_head _, ?_⟩
  simp [grayWords, gray_head]

end Toffoli
