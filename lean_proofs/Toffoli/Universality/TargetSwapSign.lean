import Toffoli.Universality.AccumulatorPermutationModel
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.Ring.Parity

namespace Toffoli
open scoped Classical

/-- Swapping the target labels exchanges one pair for each control state.
An odd number of control states therefore makes this an odd permutation. -/
theorem target_swap_sign {C K : Type*} [Fintype C] [Fintype K]
    [DecidableEq C] [DecidableEq K] [Zero K] [One K]
    (h01 : (0 : K) ≠ 1) (hC : Odd (Fintype.card C)) :
    Equiv.Perm.sign (targetSwap (C := C) (K := K)) = -1 := by
  cases Subsingleton.elim ‹DecidableEq K› (Classical.decEq K)
  rw [targetSwap, Equiv.Perm.sign_prodCongrRight]
  simp only [Equiv.Perm.sign_swap h01, Finset.prod_const, Finset.card_univ]
  exact (hC.neg_one_pow : (-1 : ℤˣ) ^ Fintype.card C = -1)

end Toffoli
