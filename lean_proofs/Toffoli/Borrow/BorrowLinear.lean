import Toffoli.Borrow.BorrowOnly
import Toffoli.Borrow.BorrowCostBound

namespace Toffoli

/-- For any coefficient, Borrow adds the scaled product on the original
d controls and target using at most 40*p*d transpositions, restoring every control. -/
theorem borrow_linear {p d : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hd : 1 ≤ d)
    (μ : ZMod p) :
    ∃ c : MultiCircuit (ZMod p) d,
      c.Realizes (fun x => μ * ∏ i, x i) ∧ c.cost ≤ 40 * p * d := by
  obtain ⟨c, hc, hcost⟩ := borrow_only hp hd μ
  refine ⟨c, hc, ?_⟩
  rw [hcost]
  exact borrow_cost_bound hp hd

end Toffoli
