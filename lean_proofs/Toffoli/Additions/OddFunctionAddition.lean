import Toffoli.Additions.OddRepresentativesCard
import Toffoli.Additions.OddBlocksCost
import Toffoli.Foundations.CircuitCostAppend

namespace Toffoli
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Complete every negation pair, then restore the control by one affine gate. -/
noncomputable def oddFunctionCircuit (f : K → K) : Circuit K :=
  oddBlocks f (oddRepresentatives K).toList ++ [.affine (-1) 0 (neg_ne_zero.mpr one_ne_zero)]

/-- An odd function over an odd-characteristic finite field is synthesized
with one transposition per nonzero negation pair. All controls are restored. -/
theorem odd_function_addition (f : K → K) (htwo : (2 : K) ≠ 0)
    (hodd : ∀ x, f (-x) = -f x) :
    (oddFunctionCircuit f).Realizes f ∧
    (oddFunctionCircuit f).cost = (Fintype.card K - 1) / 2 := by
  have hzero : f 0 = 0 := by
    simpa only [neg_zero, eq_neg_iff_add_eq_zero, ← two_mul,
      mul_eq_zero_iff_left htwo] using hodd 0
  have hpairs : ∀ a ∈ (oddRepresentatives K).toList,
      ∀ b ∈ (oddRepresentatives K).toList, a ≠ -b := by
    intro a ha b hb hab
    subst a
    exact (odd_representatives_spec K htwo b).2
      ⟨Finset.mem_toList.mp hb, Finset.mem_toList.mp ha⟩
  constructor
  · intro x t
    simp only [oddFunctionCircuit, Circuit.eval, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    change Gate.eval (.affine (-1) 0 (neg_ne_zero.mpr one_ne_zero))
      ((oddBlocks f (oddRepresentatives K).toList).eval (x, t)) = _
    rw [odd_blocks_eval f hodd _ (Finset.nodup_toList _) hpairs]
    simp only [Finset.mem_toList]
    simp only [(odd_representatives_spec K htwo x).1]
    by_cases hx : x = 0
    · simp [hx, hzero, Gate.eval]
    · simp [hx, Gate.eval]
  · rw [oddFunctionCircuit, circuit_cost_append]
    -- The final affine negation is free, so only the pair blocks contribute.
    change (oddBlocks f (oddRepresentatives K).toList).cost + 0 = _
    rw [add_zero, odd_blocks_cost, Finset.length_toList]
    exact odd_representatives_card K htwo

end Toffoli
