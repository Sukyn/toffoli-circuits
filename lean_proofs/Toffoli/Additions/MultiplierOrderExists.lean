import Toffoli.Additions.PowerMultiplierExists

namespace Toffoli

/-- Every divisor of the unit-group size occurs as a multiplier order.
Taking a suitable power of a generator is enough; no search is needed. -/
theorem multiplier_order_exists {K : Type*} [Field K] [Finite K]
    (r : ℕ) (hr : r ∣ Nat.card K - 1) :
    ∃ a : Kˣ, orderOf a = r := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  refine ⟨g ^ (orderOf g / r), orderOf_pow_orderOf_div (orderOf_pos g).ne' ?_⟩
  simpa only [hg, Nat.card_units] using hr

end Toffoli
