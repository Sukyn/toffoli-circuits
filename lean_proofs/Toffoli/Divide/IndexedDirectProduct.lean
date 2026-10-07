import Toffoli.Divide.IndexedDivideCost

namespace Toffoli

/-- Direct polarization uses singleton groups, so all preparations are free
SUMs. The compiled circuit uses only the given controls and target, restores
every control, and retains the exact count even when the scalar is zero. -/
theorem indexed_direct_product {p n : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (controls : Finset (Fin n)) (hd : 2 ≤ controls.card)
    (hdegree : controls.card ≤ p - 2)
    (target : IndexedTarget n)
    (htarget : ∀ i ∈ controls, target ≠ some i) (μ : ZMod p) :
    ∃ c : MultiCircuit (ZMod p) n,
      (∀ x t, c.eval (x, t) =
        indexedTargetAdd target (μ * ∏ i ∈ controls, x i) (x, t)) ∧
      c.cost = 2 ^ (controls.card - 1) * ((p - 1) - (p - 1) /
        leastAdmissibleOrder (p - 1) controls.card (by omega) (by omega)) := by
  let singletons := Composition.ones (controls.card - 1)
  have hpred : controls.card - 1 + 1 = controls.card := Nat.sub_add_cancel (by omega)
  have hgroupDegree : singletons.length + 1 ≤ p - 2 := by
    simpa [singletons, hpred] using hdegree
  -- Direct polarization is one grouped step whose children are all SUMs.
  have hchildren (j : Fin singletons.length) : DivideCost p (singletons.blocksFun j) 0 := by
    simpa [singletons] using DivideCost.sum (p := p)
  have htree := DivideCost.step hd singletons hgroupDegree (fun _ => 0) hchildren
  -- The general compiler supplies the wire layout, restoration, and exact cost.
  obtain ⟨c, hc, hcost, _⟩ := indexed_divide_cost hp htree controls rfl target htarget μ
  refine ⟨c, hc, ?_⟩
  simpa [divideStepCost, singletons, hpred] using hcost

end Toffoli
