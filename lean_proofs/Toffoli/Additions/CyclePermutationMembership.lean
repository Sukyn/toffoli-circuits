import Toffoli.Additions.CyclePermutationOutside

namespace Toffoli

/-- A permutation that fixes unlisted values cannot send a listed value outside. -/
theorem cycle_permutation_mem_iff_mem {K : Type*} [DecidableEq K]
    (a : K) (labels : List K) (x : K) :
    cyclePermutation a labels x ∈ a :: labels ↔ x ∈ a :: labels := by
  constructor
  · intro hx
    by_contra hout
    exact hout (by simpa only [cycle_permutation_apply_of_not_mem a labels x hout] using hx)
  · intro hx
    by_contra hout
    have hfixed := cycle_permutation_apply_of_not_mem a labels _ hout
    have heq : cyclePermutation a labels x = x :=
      (cyclePermutation a labels).injective hfixed
    exact hout (heq.symm ▸ hx)

end Toffoli
