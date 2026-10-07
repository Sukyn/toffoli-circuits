import Toffoli.Additions.CyclePermutationModel

namespace Toffoli

/-- Every anchored swap fixes an unlisted value, even if labels repeat. -/
theorem cycle_permutation_apply_of_not_mem {K : Type*} [DecidableEq K]
    (a : K) (labels : List K)
    (x : K) (hx : x ∉ a :: labels) : cyclePermutation a labels x = x := by
  induction labels with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.mem_cons, not_or] at hx
    have hx' : x ∉ a :: rest := by simpa using And.intro hx.1 hx.2.2
    simpa [cyclePermutation, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hx.1 hx.2.1] using ih hx'

end Toffoli
