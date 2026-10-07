import Toffoli.Schedules.GrayModel

namespace Toffoli

/-- Reflection creates no repetitions: the two halves have opposite first
signs, and each half inherits the old list's lack of repetitions. -/
theorem gray_words_nodup (n : ℕ) : (grayWords n).Nodup := by
  induction n with
  | zero => simp [grayWords]
  | succ n ih =>
    rw [grayWords, List.nodup_append]
    refine ⟨List.Nodup.map (Fin.cons_right_injective (n := n) (α := fun _ => Bool) false) ih,
      List.Nodup.map (Fin.cons_right_injective (n := n) (α := fun _ => Bool) true)
        (List.nodup_reverse.mpr ih), ?_⟩
    simp [List.mem_map, Fin.cons_inj]

end Toffoli
