import Toffoli.Foundations.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The zero-sum condition in `lem:power-cycles` of the paper.

A cycle is represented by a finite set together with mathlib's `IsCycleOn`
property. This includes singleton cycles, in particular the fixed point zero.
The proof works over any field; the paper's prime and degree bounds are needed
for choosing a multiplier, rather than for this cancellation argument.
-/
namespace Toffoli

open scoped BigOperators

/-- Multiplication by `a` permutes every cycle. Reindexing its power sum
therefore multiplies that same sum by `a ^ d`. If this factor differs from
one, the sum must be zero. Scaling the summands by `μ` preserves zero. -/
theorem power_cycles {K : Type*} [Field K] (a μ : K) (d : ℕ)
    (ha : a ≠ 0) (had : a ^ d ≠ 1) (C : Finset K)
    (hC : (Equiv.mulLeft₀ a ha).IsCycleOn (C : Set K)) :
    ∑ c ∈ C, μ * c ^ d = 0 := by
  classical
  have hsum : a ^ d * (∑ c ∈ C, c ^ d) = ∑ c ∈ C, c ^ d := by
    have h : (∑ c ∈ C, (a * c) ^ d) = ∑ c ∈ C, c ^ d :=
      Finset.sum_equiv (Equiv.mulLeft₀ a ha)
        (fun c => hC.apply_mem_iff.symm) (fun _ _ => rfl)
    simpa only [Equiv.mulLeft₀_apply, mul_pow, Finset.mul_sum] using h
  have hzero : (∑ c ∈ C, c ^ d) = 0 := eq_zero_of_mul_eq_self_left had hsum
  rw [← Finset.mul_sum, hzero, mul_zero]

end Toffoli
