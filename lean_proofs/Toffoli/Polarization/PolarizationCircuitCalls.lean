import Toffoli.Polarization.PolarizationWalkCalls
import Toffoli.Schedules.GrayFlipsCount
import Toffoli.Schedules.GrayFlipsLength
import Mathlib.Data.List.FinRange

namespace Toffoli

/-- Initial preparation and final restoration each add one call per group.
The intervening calls are precisely the Gray flips. -/
theorem polarization_circuit_calls {K : Type*} [CommRing K] {n : ℕ}
    (normalization : K) :
    polarizationPowerCalls (polarizationCircuit (n := n) normalization) = 2 ^ n ∧
      ∀ i : Fin n, (polarizationGroupCalls (polarizationCircuit normalization)).count i =
        2 + 2 ^ i.val := by
  obtain ⟨hg, hp⟩ := polarization_walk_calls normalization (fun _ => false) (grayFlips n)
  simp only [polarizationGroupCalls, polarizationPowerCalls] at hg hp
  constructor
  · simpa [polarizationCircuit, polarizationPowerCalls, List.ofFn_eq_map,
      List.filter_map, Function.comp_def, hp] using gray_flips_length n
  · intro i
    have hi : (List.finRange n).count i = 1 :=
      List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange i)
    simp [polarizationCircuit, polarizationGroupCalls, List.ofFn_eq_map,
      List.filterMap_map, hg, hi, gray_flips_count]
    omega

end Toffoli
