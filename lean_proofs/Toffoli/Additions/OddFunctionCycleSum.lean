import Toffoli.Foundations.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! A supporting step for `cor:odd-function-addition`.
This proves the cycle condition; it does not claim the circuit or its cost.
-/
namespace Toffoli

open scoped BigOperators

/-- An odd function sums to zero on any cycle of negation, over a field
whose characteristic is not two. Reindex the sum by negation: it equals
its own negative, so twice the sum is zero. -/
theorem odd_function_cycle_sum {K : Type*} [Field K] (htwo : (2 : K) ≠ 0)
    (f : K → K) (hodd : ∀ x, f (-x) = -f x) (C : Finset K)
    (hC : (Equiv.neg K).IsCycleOn (C : Set K)) :
    ∑ c ∈ C, f c = 0 := by
  classical
  have hsum : -(∑ c ∈ C, f c) = ∑ c ∈ C, f c := by
    have h : (∑ c ∈ C, f (-c)) = ∑ c ∈ C, f c :=
      Finset.sum_equiv (Equiv.neg K)
        (fun c => hC.apply_mem_iff.symm) (fun _ _ => rfl)
    simpa only [hodd, Finset.sum_neg_distrib] using h
  have hzero : (2 : K) * (∑ c ∈ C, f c) = 0 :=
    (two_mul _).trans (eq_neg_iff_add_eq_zero.mp hsum.symm)
  exact (mul_eq_zero.mp hzero).resolve_left htwo

end Toffoli
