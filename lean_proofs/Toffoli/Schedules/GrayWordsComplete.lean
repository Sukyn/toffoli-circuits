import Toffoli.Schedules.GrayModel

namespace Toffoli

/-- Every sign assignment occurs in reflected Gray order. -/
theorem mem_gray_words (n : ℕ) (word : GrayWord n) : word ∈ grayWords n := by
  induction n with
  | zero => exact List.mem_singleton.mpr (Subsingleton.elim _ _)
  | succ n ih =>
    obtain ⟨b, tail, rfl⟩ := Fin.exists_cons word
    cases b <;> simp [grayWords, ih]

end Toffoli
