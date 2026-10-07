import Toffoli.Borrow.BorrowProduct
import Toffoli.Borrow.BorrowCostModel

namespace Toffoli

/-- Borrow realizes every scaled product on the original wires,
with the paper's exact count, including the SUM and Toffoli base cases.
Zero coefficients use the same construction. -/
theorem borrow_only {p d : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hd : 1 ≤ d)
    (μ : ZMod p) :
    ∃ c : MultiCircuit (ZMod p) d,
      c.Realizes (fun x => μ * ∏ i, x i) ∧
      c.cost = borrowCost (2 * optimalSquareCost p hp) d := by
  by_cases hsmall : d ≤ 2
  · obtain ⟨c, hc, hcost⟩ := indexed_product (n := d) hp Finset.univ ∅
      (Finset.card_pos.mp (by simpa using hd))
      (by simp; omega) (by simp) none (by simp) μ
    exact ⟨c, by simpa only [indexedTargetAdd] using hc,
      by simpa [borrowCost, hsmall] using hcost⟩
  · simpa only [borrowCost, if_neg hsmall] using borrow_product hp (by omega) μ

end Toffoli
