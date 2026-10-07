import Toffoli.Foundations.ProductConstructionModel
import Toffoli.Mixed.MixedPolarizationLayout
import Toffoli.Polarization.IndexedGroupedPolarizationLocal
import Toffoli.Foundations.CircuitLocalityPromote
import Toffoli.Divide.DivideLayoutProduct
import Toffoli.Divide.DivideModel

namespace Toffoli

/-- Compile the polarization branch of the mixed recurrence. A preparation
may borrow every available wire except its own controls, its destination,
and the parent target. The reserved control is restored by polarization;
all excluded ancestor targets remain protected at each primitive gate. -/
theorem mixed_polarization {p d b : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hd : 3 ≤ d) (c : Composition (d - 1)) (hdegree : c.length + 1 ≤ p - 2)
    (q : Fin c.length → ℕ)
    (children : ∀ j, ProductConstruction (ZMod p) (c.blocksFun j)
      (d + b - c.blocksFun j - 1) (q j)) :
    ProductConstruction (ZMod p) d b (divideStepCost p c hdegree q) := by
  classical
  intro n controls pool hsubset hcard hpool target htarget μ
  obtain ⟨first, hfirst, groups, hcards, hchildSubset, hdisjoint, hcover, hbudget⟩ :=
    mixed_polarization_layout pool controls hsubset hcard hpool (by omega) c
  have hfirstPool : first ∈ pool := hsubset hfirst
  have hchildTarget : ∀ i ∈ pool.erase first, (some first : IndexedTarget n) ≠ some i := by
    intro i hi
    simpa only [ne_eq, Option.some.injEq] using (Finset.mem_erase.mp hi).1.symm
  -- The induction hypotheses use the exact child pools from the recurrence.
  choose group hgroup hcost hlocal using
    (fun j (a : ZMod p) => children j (groups j) (pool.erase first)
      (hchildSubset j) (hcards j) (hbudget j).1 (some first) hchildTarget a)
  have hfirstNot (j : Fin c.length) : first ∉ groups j :=
    (Finset.subset_erase.mp (hchildSubset j)).2
  have hgroupSubset (j : Fin c.length) : groups j ⊆ pool :=
    (Finset.subset_erase.mp (hchildSubset j)).1
  have hparentLocal (j : Fin c.length) (a : ZMod p) :
      (group j a).AccumulatorLocal pool target :=
    circuit_locality_promote (group j a) (pool.erase first) pool
      (Finset.erase_subset first pool) first hfirstPool target htarget (hlocal j a)
  obtain ⟨circuit, hrun, hcount, hprotected⟩ := indexed_grouped_polarization_local
    hp hdegree pool first hfirstPool target htarget groups hfirstNot hgroupSubset
    group q (by simpa only [indexedTargetAdd] using hgroup) hcost hparentLocal μ
  refine ⟨circuit, ?_, hcount, hprotected⟩
  intro x t
  have hproduct := divide_layout_product controls hfirst groups hdisjoint hcover x
  simpa only [mul_assoc, hproduct] using hrun x t

end Toffoli
