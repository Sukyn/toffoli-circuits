import Toffoli.Additions.PowerCycleModel

namespace Toffoli

/-- Admissibility gives the paper's canonical primitive circuit, with its
exact cost. The same cycle listing is used for behavior and counting. -/
theorem power_cycle_synthesis {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (a b μ : K) (ha : a ≠ 0) (d : ℕ)
    (hadm : PowerCycleAdmissible a b μ ha d) :
    (powerCycleCircuit a b μ ha d).Realizes (fun x => μ * x ^ d) ∧
      (powerCycleCircuit a b μ ha d).cost = affineCycleCost a b ha := by
  obtain ⟨hn, hcover, hperm, _, hc⟩ :=
    Classical.choose_spec (exists_cycle_listing (affineControl a b ha))
  constructor
  · exact (cycle_synthesis_correct a b ha _ (fun x => μ * x ^ d) hn hcover hperm
      ((cycle_listing_zero_sum_iff _ _ hn hcover hc _).2 hadm)).1
  · exact cycle_addition_count a b ha (fun x => μ * x ^ d)

end Toffoli
