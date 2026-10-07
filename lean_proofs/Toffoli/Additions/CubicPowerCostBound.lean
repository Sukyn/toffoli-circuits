import Toffoli.Additions.AdmissibleOrderCost
import Mathlib.Data.Nat.Prime.Basic

namespace Toffoli

/-- The four cube additions in a cubic polarization step cost at most
2*(p-1): order two is admissible because p is odd and two does not divide three. -/
theorem cubic_power_cost_bound {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    4 * ((p - 1) - (p - 1) /
      leastAdmissibleOrder (p - 1) 3 (by decide) (by omega)) ≤ 2 * (p - 1) := by
  have heven : 2 ∣ p - 1 :=
    ((Fact.out : p.Prime).even_sub_one (by omega)).two_dvd
  let r := leastAdmissibleOrder (p - 1) 3 (by decide) (by omega)
  obtain ⟨⟨hrpos, _, _⟩, hleast⟩ :=
    least_admissible_order_spec (p - 1) 3 (by decide) (by omega)
  have hrle : r ≤ 2 := hleast 2 (by decide) heven (by decide)
  have hcost := admissible_order_cost_mono (p - 1) r 2 hrpos hrle
  have hhalf : (p - 1) / 2 * 2 = p - 1 := Nat.div_mul_cancel heven
  calc
    _ ≤ 4 * ((p - 1) - (p - 1) / 2) := Nat.mul_le_mul_left 4 hcost
    _ = 2 * (p - 1) := by omega

end Toffoli
