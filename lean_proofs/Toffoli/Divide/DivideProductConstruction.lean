import Toffoli.Foundations.ProductConstructionModel
import Toffoli.Divide.IndexedDivideCost
import Toffoli.Foundations.CircuitLocalityMono

namespace Toffoli

/-- Every Divide tree supplies a product construction with any borrowed-wire
budget. Its circuit needs only the controls; enlarging the allowed pool
preserves the same execution, exact cost, and gatewise locality. -/
theorem divide_product_construction {p d cost : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (tree : DivideCost p d cost) (b : ℕ) :
    ProductConstruction (ZMod p) d b cost := by
  intro n controls pool hsubset hcard _hpool target htarget μ
  obtain ⟨circuit, hrun, hcost, hlocal⟩ :=
    indexed_divide_cost hp tree controls hcard target
      (fun i hi => htarget i (hsubset hi)) μ
  exact ⟨circuit, hrun, hcost, circuit_locality_mono hlocal hsubset htarget⟩

end Toffoli
