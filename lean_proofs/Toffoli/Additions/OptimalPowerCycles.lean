import Toffoli.Additions.PowerCycleAffineCases
import Toffoli.Additions.PowerCycleSynthesis
import Toffoli.Additions.PowerCycleCostFormula
import Toffoli.Additions.MultiplierAdmissible
import Toffoli.Additions.MultiplierOrderExists
import Toffoli.Additions.MultiplierCycleCount
import Toffoli.Additions.TranslationCycleCount
import Toffoli.Additions.AdmissibleOrderCost

namespace Toffoli

/-- The least admissible order is attained. Every multiplier of that order
produces a realizing circuit at the stated cost, and no admissible affine
choice costs less. Optimality is within the paper's cycle algorithm. -/
theorem optimal_power_cycles {p : ℕ} [Fact p.Prime]
    (μ : ZMod p) (hμ : μ ≠ 0) (d : ℕ) (hd : 0 < d) (hbound : d < p - 1) :
    let r := leastAdmissibleOrder (p - 1) d hd hbound
    (∃ a : (ZMod p)ˣ, orderOf a = r) ∧
    (∀ a : (ZMod p)ˣ, orderOf a = r →
      (powerCycleCircuit (a : ZMod p) 0 μ a.ne_zero d).Realizes (fun x => μ * x ^ d) ∧
      (powerCycleCircuit (a : ZMod p) 0 μ a.ne_zero d).cost = (p - 1) - (p - 1) / r) ∧
    (∀ a b : ZMod p, ∀ ha : a ≠ 0, PowerCycleAdmissible a b μ ha d →
      (p - 1) - (p - 1) / r ≤ affineCycleCost a b ha) ∧
    (((p - 1) - (p - 1) / r : ℕ) : ℚ) =
      ((p - 1 : ℕ) : ℚ) * (1 - 1 / (r : ℚ)) := by
  classical
  let r := leastAdmissibleOrder (p - 1) d hd hbound
  obtain ⟨⟨hrpos, hrdiv, hrnot⟩, hmin⟩ :=
    least_admissible_order_spec (p - 1) d hd hbound
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply multiplier_order_exists (K := ZMod p) r
    simpa [Nat.card_eq_fintype_card, ZMod.card] using hrdiv
  · intro a horder
    have hadm : PowerCycleAdmissible (a : ZMod p) 0 μ a.ne_zero d :=
      (multiplier_admissible_iff a μ hμ d).mpr (by simpa [horder] using hrnot)
    have hs := power_cycle_synthesis (a : ZMod p) 0 μ a.ne_zero d hadm
    refine ⟨hs.1, ?_⟩
    rw [hs.2, multiplier_cycle_count, ZMod.card, horder]
  · intro a b ha hadm
    rcases power_cycle_affine_cases a b μ ha d hμ hadm with ⟨hb, _⟩ | ⟨haone, hb⟩
    · subst b
      let u : (ZMod p)ˣ := Units.mk0 a ha
      have hnot : ¬orderOf u ∣ d :=
        (multiplier_admissible_iff u μ hμ d).mp hadm
      have hdiv : orderOf u ∣ p - 1 := by
        simpa [Nat.card_units, Nat.card_eq_fintype_card, ZMod.card, Nat.totient_prime (Fact.out : p.Prime)] using
          (orderOf_dvd_natCard u)
      have hleast := hmin (orderOf u) (orderOf_pos u) hdiv hnot
      have hcost : affineCycleCost a 0 ha = (p - 1) - (p - 1) / orderOf u := by
        simpa [u, ZMod.card] using multiplier_cycle_count u
      rw [hcost]
      exact admissible_order_cost_mono (p - 1) r (orderOf u) hrpos hleast
    · subst a
      rw [translation_cycle_count b hb]
      exact Nat.sub_le _ _
  · exact power_cycle_cost_formula (p - 1) r hrdiv

end Toffoli
