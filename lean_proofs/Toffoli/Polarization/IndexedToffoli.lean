import Toffoli.Divide.IndexedDivideCost
import Toffoli.Divide.DivideCountTwo

namespace Toffoli

/-- The two-control polarization construction has a local witness for every
scalar, including zero. Its single preparation is a SUM, so only the two
square additions contribute to the transposition count. -/
theorem indexed_toffoli {p n : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (i j : Fin n) (hij : i ≠ j) (target : IndexedTarget n)
    (hti : target ≠ some i) (htj : target ≠ some j) (μ : ZMod p) :
    ∃ c : MultiCircuit (ZMod p) n,
      (∀ x t, c.eval (x, t) = indexedTargetAdd target (μ * x i * x j) (x, t)) ∧
      c.cost = 2 * optimalSquareCost p hp ∧ c.AccumulatorLocal {i, j} target := by
  -- Reuse the attained two-control construction and its known exact count.
  have htree := (divide_count_spec hp (by decide : 0 < 2)).1
  have htarget : ∀ k ∈ ({i, j} : Finset (Fin n)), target ≠ some k := by
    simpa only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq] using
      And.intro hti htj
  obtain ⟨c, hrun, hcost, hlocal⟩ := indexed_divide_cost hp htree
    {i, j} (Finset.card_pair hij) target htarget μ
  refine ⟨c, ?_, ?_, hlocal⟩
  · intro x t
    simpa only [Finset.prod_pair hij, mul_assoc] using hrun x t
  · simpa only [divide_count_two hp] using hcost

end Toffoli
