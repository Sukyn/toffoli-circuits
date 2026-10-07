import Toffoli.Additions.CycleAmountsFamilyCanonical
import Toffoli.Additions.CycleSynthesis

namespace Toffoli
variable {K : Type*} [Field K] [DecidableEq K]

/-- The same primitive gate list is obtained from the unrestricted amount model
by supplying the paper's canonical prefix sums. -/
theorem cycleSynthesisWithAmounts_canonical (a b : K) (ha : a ≠ 0)
    (cycles : List (List K)) (f : K → K) (hn : cycles.flatten.Nodup) :
    cycleSynthesisWithAmounts a b ha cycles (canonicalFamilyAmounts cycles f) =
      cycleSynthesis a b ha cycles f := by
  rw [cycleSynthesisWithAmounts, cycleSynthesis,
    cycleFamilyWithAmounts_canonical cycles f hn]

end Toffoli
