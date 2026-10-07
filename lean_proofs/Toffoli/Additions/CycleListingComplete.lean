import Toffoli.Additions.CycleListing

namespace Toffoli
variable {α : Type*} [DecidableEq α]

/-- A covering list of actual cycles includes every nonempty cycle. Two
cycles sharing a point are both its orbit under integer powers of σ. -/
theorem cycle_listing_complete (σ : Equiv.Perm α) (cycles : List (List α))
    (hcover : ∀ x, x ∈ cycles.flatten)
    (hc : ∀ labels ∈ cycles, σ.IsCycleOn {x | x ∈ labels})
    (C : Finset α) (hC : σ.IsCycleOn (C : Set α)) (hne : C.Nonempty) :
    ∃ labels ∈ cycles, labels.toFinset = C := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨labels, hl, hxl⟩ := List.mem_flatten.mp (hcover x)
  refine ⟨labels, hl, ?_⟩
  apply Finset.coe_injective
  have hset := ((hc labels hl).range_zpow hxl).symm.trans (hC.range_zpow hx)
  simpa using hset

end Toffoli
