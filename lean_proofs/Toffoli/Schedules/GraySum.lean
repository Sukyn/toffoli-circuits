import Toffoli.Schedules.GrayWordsComplete
import Toffoli.Schedules.GrayWordsNodup
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Toffoli

/-- Summing in Gray order is the same finite sum as summing over all sign
assignments. This connects the executable walk to Fischer's identity. -/
theorem gray_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (f : GrayWord n → M) :
    ((grayWords n).map f).sum = ∑ word, f word := by
  classical
  rw [← List.sum_toFinset f (gray_words_nodup n)]
  have h : (grayWords n).toFinset = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr (fun word => List.mem_toFinset.mpr (mem_gray_words n word))
  rw [h]

end Toffoli
