import Toffoli.Additions.PowerCycleModel
import Toffoli.Additions.PowerCyclesByOrder
import Toffoli.Additions.MultiplierCyclePower
import Mathlib.Algebra.Field.ZMod

namespace Toffoli

/-- A multiplier is admissible exactly when its order does not divide the
power. For necessity, its cycle through 1 has a nonzero constant power sum. -/
theorem multiplier_admissible_iff {p : ℕ} [Fact p.Prime]
    (a : (ZMod p)ˣ) (μ : ZMod p) (hμ : μ ≠ 0) (d : ℕ) :
    PowerCycleAdmissible (a : ZMod p) 0 μ a.ne_zero d ↔ ¬orderOf a ∣ d := by
  classical
  have heq : affineControl (a : ZMod p) 0 a.ne_zero =
      Equiv.mulLeft₀ (a : ZMod p) a.ne_zero := by
    ext x
    simp [affineControl]
  constructor
  · intro hadm hd
    have hpow : (a : ZMod p) ^ d = 1 := by
      exact congrArg Units.val (orderOf_dvd_iff_pow_eq_one.mp hd)
    obtain ⟨cycles, _, hcover, _, _, hc⟩ :=
      exists_cycle_listing (Equiv.mulLeft₀ (a : ZMod p) a.ne_zero)
    obtain ⟨labels, hl, h1⟩ := List.mem_flatten.mp (hcover 1)
    let C := labels.toFinset
    have hC : (Equiv.mulLeft₀ (a : ZMod p) a.ne_zero).IsCycleOn (C : Set (ZMod p)) := by
      simpa [C] using hc labels hl
    have h1C : (1 : ZMod p) ∈ C := by simpa [C] using h1
    have hzero : (0 : ZMod p) ∉ C := by
      intro hz
      exact zero_ne_one ((hC.2 hz h1C).eq_of_left (by simp [Function.IsFixedPt]))
    have hpositive : 0 < C.card := Finset.card_pos.mpr ⟨1, h1C⟩
    have hsmall : C.card < p := by
      simpa only [ZMod.card] using Finset.card_lt_univ_of_notMem hzero
    have hcast : (C.card : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt hpositive hsmall
    have hxpow (x : ZMod p) (hx : x ∈ C) : x ^ d = 1 := by
      obtain ⟨n, _, hn⟩ := hC.exists_pow_eq h1C hx
      rw [← hn, multiplier_pow_apply, mul_one, ← pow_mul, Nat.mul_comm n d,
        pow_mul, hpow, one_pow]
    have hsum : (∑ x ∈ C, μ * x ^ d) = (C.card : ZMod p) * μ := by
      calc
        _ = ∑ _x ∈ C, μ := Finset.sum_congr rfl (fun x hx => by rw [hxpow x hx, mul_one])
        _ = _ := by simp [nsmul_eq_mul]
    exact mul_ne_zero hcast hμ (hsum.symm.trans (hadm C (by simpa only [heq] using hC)))
  · intro hd C hC
    apply power_cycles_by_order a μ d hd C
    simpa only [heq] using hC

end Toffoli
