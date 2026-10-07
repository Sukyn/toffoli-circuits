import Toffoli.Universality.ProductRegisterGeneration
import Toffoli.Universality.BalancedAdditionFromControlPermutations
import Toffoli.Universality.BalancedThreeCycle
import Toffoli.Universality.RingAffineSwapPreprimitive
import Toffoli.Universality.IsThreeCyclePermCongr
import Toffoli.Universality.TargetSwapSign
import Toffoli.Universality.AlternatingAndOdd
import Mathlib.GroupTheory.GroupAction.Jordan

namespace Toffoli
open scoped Classical

/-- Universality on the controls extends to one more wire. Two balanced
additions isolate a three-cycle; double transitivity and the odd local swap
then give every permutation of the larger register. -/
theorem odd_ring_register_step {R : Type*} [CommRing R]
    [Fintype R] [DecidableEq R]
    (hodd : Odd (Fintype.card R)) (hcard : 5 ≤ Fintype.card R)
    (hone : affineSwapGroup R (Equiv.swap (0 : R) 1) = ⊤)
    {n : ℕ} (hn : 0 < n)
    (hcontrols : affineSwapGroup R
      (coordinatePermutation (⟨0, hn⟩ : Fin n) (Equiv.swap (0 : R) 1)) = ⊤) :
    affineSwapGroup R
      (coordinatePermutation (0 : Fin (n + 1)) (Equiv.swap (0 : R) 1)) = ⊤ := by
  cases Subsingleton.elim ‹DecidableEq R› (Classical.decEq R)
  letI : Nontrivial R := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  -- The cardinality is zero in the ring; in characteristic two an odd
  -- cardinality would instead be one.
  have htwo : (2 : R) ≠ 0 := by
    intro h
    have hcard_one := natCast_eq_one_of_odd_of_two_eq_zero hodd h
    rw [Nat.cast_card_eq_zero] at hcard_one
    exact zero_ne_one hcard_one
  let C := Controls R n
  let G := affineSwapGroup R (targetSwap (C := C) (K := R))
  let H := affineSwapGroup R
    (coordinatePermutation (0 : Fin (n + 1)) (Equiv.swap (0 : R) 1))
  obtain ⟨control_mem, target_mem⟩ := product_register_generation hn hone hcontrols
  have affine_mem (e : (C × R) ≃ᵃ[R] (C × R)) : e.toEquiv ∈ G :=
    Subgroup.subset_closure (Or.inl ⟨e, rfl⟩)
  let a : C := fun _ => 0
  let b : C := fun _ => 1
  let c : C := fun _ => 2
  let i : Fin n := ⟨0, hn⟩
  have hab : a ≠ b := fun h => zero_ne_one (congrFun h i)
  have hac : a ≠ c := fun h => htwo (congrFun h i).symm
  have hbc : b ≠ c := by
    intro h
    apply zero_ne_one (α := R)
    exact add_left_cancel (show (1 : R) + 0 = 1 + 1 by
      simpa only [add_zero, one_add_one_eq_two] using congrFun h i)
  obtain ⟨g, hg, hthree⟩ := balanced_three_cycle htwo hcard a b c hab hac hbc G target_mem
    (balanced_addition_from_control_permutations hn G control_mem affine_mem a b hab)
    (balanced_addition_from_control_permutations hn G control_mem affine_mem a c hac)

  -- Move the product presentation back to the manuscript's register.
  let e := registerJoin (K := R) n
  have hgate : e.toEquiv.permCongr (targetSwap (C := C) (K := R)) =
      coordinatePermutation (0 : Fin (n + 1)) (Equiv.swap (0 : R) 1) := by
    change (registerJoin (K := R) n).toEquiv.permCongr (targetSwap (C := C) (K := R)) = _
    rw [← register_target_swap (K := R) n]
    rw [AffineEquiv.toEquiv_symm, ← Equiv.permCongr_symm, Equiv.apply_symm_apply]
  have hmem : e.toEquiv.permCongr g ∈ H := by
    simpa only [hgate] using affine_swap_conjugate_mem e _ g hg
  have hAlt : alternatingGroup (Controls R (n + 1)) ≤ H :=
    Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
      (ring_affine_swap_preprimitive (0 : Fin (n + 1)) hone)
      (is_three_cycle_perm_congr e.toEquiv hthree) hmem
  have hs_mem : e.toEquiv.permCongr (targetSwap (C := C) (K := R)) ∈ H := by
    rw [hgate]
    exact Subgroup.subset_closure (Or.inr rfl)
  have hC : Odd (Fintype.card C) := by
    simpa only [C, Controls, Fintype.card_fun, Fintype.card_fin] using hodd.pow (n := n)
  have hsign : Equiv.Perm.sign
      (e.toEquiv.permCongr (targetSwap (C := C) (K := R))) = -1 := by
    rw [Equiv.Perm.sign_permCongr]
    exact target_swap_sign zero_ne_one hC
  exact alternating_and_odd H hAlt _ hs_mem hsign

end Toffoli
