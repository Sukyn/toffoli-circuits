import Toffoli.Additions.CycleTransferBlock
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Toffoli
open scoped BigOperators
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- A zero-sum table is the sum of transfers from zero to each nonzero label.
This is the constructive algebraic step in `thm:accumulator-zero-sum`.
-/
theorem transfer_decomposition (f : K → K) (h : ∑ x, f x = 0) (x : K) :
    ∑ b ∈ Finset.univ.erase (0 : K), transferIncrement 0 b (f b) x = f x := by
  by_cases hx : x = 0
  · subst x
    have hs : (∑ b ∈ Finset.univ.erase (0 : K), f b) + f 0 = 0 := by
      rw [Finset.sum_erase_add _ _ (by simp), h]
    have he : (∑ b ∈ Finset.univ.erase (0 : K), f b) = -f 0 :=
      eq_neg_of_add_eq_zero_left hs
    simp [transferIncrement, he]
  · rw [Finset.sum_eq_single x]
    · simp [transferIncrement, hx]
    · intro b hb hbx
      simp [transferIncrement, hx, Ne.symm hbx]
    · intro hnot
      exact False.elim (hnot (by simp [hx]))

end Toffoli
