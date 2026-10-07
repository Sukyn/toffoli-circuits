import Toffoli.Additions.CycleAmountsCanonicalModel
import Toffoli.Additions.CycleAmountsCongr
import Toffoli.Additions.CycleTransfers

namespace Toffoli
variable {K : Type*} [Field K] [DecidableEq K]

/-- The unrestricted-amount model contains the paper's prefix-sum construction. -/
theorem cycleTransfersWithAmounts_canonical (a : K) (labels : List K)
    (f : K → K) (hn : (a :: labels).Nodup) :
    cycleTransfersWithAmounts a labels (canonicalTransferAmounts a labels f) =
      cycleTransfers a labels f := by
  induction labels generalizing f with
  | nil => rfl
  | cons b rest ih =>
    have hb : b ∉ rest := (List.nodup_cons.mp hn.of_cons).1
    have hn' : (a :: rest).Nodup := hn.sublist (by simp)
    simp only [cycleTransfersWithAmounts, canonicalTransferAmounts,
      Function.update_self, cycleTransfers]
    congr 1
    rw [cycleTransfersWithAmounts_congr a rest _
      (canonicalTransferAmounts a rest (Function.update f a (f a + f b)))]
    · exact ih _ hn'
    · intro x hx
      have hxb : x ≠ b := fun h => hb (h ▸ hx)
      simp [hxb]

end Toffoli
