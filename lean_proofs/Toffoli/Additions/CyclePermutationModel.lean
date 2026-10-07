import Mathlib.GroupTheory.Perm.List

/-! The control permutation of a cycle-transfer circuit. Multiplication of
permutations acts right to left: the first listed swap runs before the
recursively constructed tail. Thus `(a b c)` sends `a` to `b`, not to `c`.
-/
namespace Toffoli

/-- Execute the anchored swaps `(a b)` in the order given by `labels`. -/
def cyclePermutation {K : Type*} [DecidableEq K] (a : K) : List K → Equiv.Perm K
  | [] => 1
  | b :: bs => cyclePermutation a bs * Equiv.swap a b

end Toffoli
