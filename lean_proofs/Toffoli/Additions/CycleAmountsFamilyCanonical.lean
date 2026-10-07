import Toffoli.Additions.CycleAmountsCanonical
import Toffoli.Additions.CycleAmountsFamilyCongr
import Toffoli.Additions.CycleFamily

namespace Toffoli
variable {K : Type*} [Field K] [DecidableEq K]

/-- One amount table reproduces every prefix-sum circuit in a disjoint family. -/
theorem cycleFamilyWithAmounts_canonical (cycles : List (List K)) (f : K → K)
    (hn : cycles.flatten.Nodup) :
    cycleFamilyWithAmounts cycles (canonicalFamilyAmounts cycles f) =
      cycleFamilyCircuit cycles f := by
  induction cycles with
  | nil => rfl
  | cons labels rest ih =>
    obtain ⟨hlabels, hrest, hdisjoint⟩ := List.nodup_append'.mp
      (show (labels ++ rest.flatten).Nodup by simpa using hn)
    cases labels with
    | nil => simpa [cycleFamilyWithAmounts, cycleFamilyCircuit, cycleWithAmounts,
        cycleCircuit, canonicalFamilyAmounts] using ih hrest
    | cons a labels =>
      simp only [cycleFamilyWithAmounts, cycleFamilyCircuit, List.flatMap_cons,
        cycleWithAmounts, cycleCircuit]
      apply congrArg₂ (fun first rest : Circuit K => first ++ rest)
      · trans cycleTransfersWithAmounts a labels (canonicalTransferAmounts a labels f)
        · apply cycleTransfersWithAmounts_congr
          intro x hx
          have hx' : x ∈ a :: labels := by simp [hx]
          simp only [canonicalFamilyAmounts, if_pos hx']
        · exact cycleTransfersWithAmounts_canonical a labels f hlabels
      · trans cycleFamilyWithAmounts rest (canonicalFamilyAmounts rest f)
        · apply cycleFamilyWithAmounts_congr
          intro x hx
          have hx' : x ∉ a :: labels := List.disjoint_right.mp hdisjoint hx
          simp only [canonicalFamilyAmounts, if_neg hx']
        · exact ih hrest

end Toffoli
