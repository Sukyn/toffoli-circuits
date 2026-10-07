import Toffoli.Additions.CycleListingZeroSumIff
import Toffoli.Additions.CycleAmountsNecessary
import Toffoli.Additions.CycleAmountsSynthesisCanonical

namespace Toffoli
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Choose a complete cycle listing, including the fixed points. -/
noncomputable def permutationCycleLists (σ : Equiv.Perm K) : List (List K) :=
  Classical.choose (exists_cycle_listing σ)

/-- The paper's cycle characterization: suitable star-transfer amounts exist
exactly when f sums to zero on every actual cycle of the affine control map.
The listing is obtained from Mathlib, rather than assumed as an input. -/
theorem cycle_addition (a b : K) (ha : a ≠ 0) (f : K → K) :
    (∃ amounts : K → K, (cycleSynthesisWithAmounts a b ha
      (permutationCycleLists (affineControl a b ha)) amounts).Realizes f) ↔
    (∀ C : Finset K, (affineControl a b ha).IsCycleOn (C : Set K) →
      ∑ x ∈ C, f x = 0) := by
  let cycles := permutationCycleLists (affineControl a b ha)
  obtain ⟨hn, hcover, hperm, _, hcycles⟩ :=
    Classical.choose_spec (exists_cycle_listing (affineControl a b ha))
  change (∃ amounts, (cycleSynthesisWithAmounts a b ha cycles amounts).Realizes f) ↔ _
  rw [← cycle_listing_zero_sum_iff (affineControl a b ha) cycles hn hcover hcycles f]
  constructor
  · rintro ⟨amounts, h⟩ labels hl
    exact cycle_synthesis_zero_sum_necessary a b ha cycles amounts f hn h labels hl
  · intro hs
    refine ⟨canonicalFamilyAmounts cycles f, ?_⟩
    rw [cycleSynthesisWithAmounts_canonical a b ha cycles f hn]
    exact (cycle_synthesis_correct a b ha cycles f hn hcover hperm hs).1

end Toffoli
