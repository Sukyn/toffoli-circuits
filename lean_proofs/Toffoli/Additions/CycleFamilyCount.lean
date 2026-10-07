import Toffoli.Additions.CycleFamilyCost
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

namespace Toffoli

/-- A covering list of disjoint nonempty cycles costs one less than its number
of labels per cycle, hence exactly the field size minus the number of cycles. -/
theorem cycleFamily_count {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (cycles : List (List K)) (f : K → K)
    (hn : cycles.flatten.Nodup) (hcover : ∀ x, x ∈ cycles.flatten)
    (hne : ∀ labels ∈ cycles, labels ≠ []) :
    (cycleFamilyCircuit cycles f).cost = Fintype.card K - cycles.length := by
  have hcost : (cycles.map (fun labels => labels.length - 1)).sum =
      cycles.flatten.length - cycles.length := by
    simpa [← List.length_flatten] using
      (Multiset.sum_map_tsub (cycles : Multiset (List K))
        (f := List.length) (g := fun _ => 1)
        (fun labels hl => List.length_pos_iff.mpr (hne labels hl)))
  have hu : cycles.flatten.toFinset = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr (fun x => List.mem_toFinset.mpr (hcover x))
  have hc : cycles.flatten.length = Fintype.card K := by
    rw [← List.toFinset_card_of_nodup hn, hu, Finset.card_univ]
  rw [cycleFamily_cost, hcost, hc]

end Toffoli
