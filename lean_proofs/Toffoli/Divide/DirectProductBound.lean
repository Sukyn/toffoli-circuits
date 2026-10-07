import Toffoli.Divide.IndexedDirectProduct
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

namespace Toffoli

/-- Direct polarization gives a circuit with a uniform exponential bound
throughout its degree range. The constant does not depend on p or d. -/
theorem direct_product_bound {p d : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hd : 2 ≤ d) (hdegree : d ≤ p - 2) (μ : ZMod p) :
    ∃ c : MultiCircuit (ZMod p) d,
      c.Realizes (fun x => μ * ∏ i, x i) ∧ c.cost ≤ p * 2 ^ d := by
  obtain ⟨c, hc, hcost⟩ := indexed_direct_product hp
    (Finset.univ : Finset (Fin d)) (by simpa using hd)
    (by simpa using hdegree) none (by simp) μ
  refine ⟨c, by simpa only [indexedTargetAdd] using hc, ?_⟩
  rw [hcost]
  simp only [Finset.card_univ, Fintype.card_fin]
  calc
    _ ≤ 2 ^ d * p := Nat.mul_le_mul
      (pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (Nat.sub_le d 1))
      ((Nat.sub_le _ _).trans (Nat.sub_le p 1))
    _ = p * 2 ^ d := Nat.mul_comm _ _

end Toffoli
