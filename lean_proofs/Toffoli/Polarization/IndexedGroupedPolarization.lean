import Toffoli.Polarization.CompiledGroupedPolarization
import Toffoli.Additions.IndexedPower
import Mathlib.Tactic.Choose

namespace Toffoli

/-- Given group circuits that prepare the first control and restore every
other wire, construct the power circuits and combine them on the chosen wires.
The result restores every wire except the selected target and has the stated
weighted cost. The group circuits and their costs are inputs; this theorem
does not minimize over groupings. -/
theorem indexed_grouped_polarization {p m n : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hdegree : m + 1 ≤ p - 2)
    (first : Fin n) (target : IndexedTarget n) (hfirst : target ≠ some first)
    (groups : Fin m → Finset (Fin n))
    (hgroups : ∀ j, first ∉ groups j)
    (htarget : ∀ j, ∀ k ∈ groups j, target ≠ some k)
    (group : Fin m → ZMod p → MultiCircuit (ZMod p) n) (q : Fin m → ℕ)
    (hgroup : ∀ j a x t, (group j a).eval (x, t) =
      (Function.update x first (x first + a * ∏ k ∈ groups j, x k), t))
    (hcost : ∀ j a, (group j a).cost = q j) (μ : ZMod p) :
    ∃ c : MultiCircuit (ZMod p) n,
      (∀ x t, c.eval (x, t) = indexedTargetAdd target
        (μ * x first * ∏ j, ∏ k ∈ groups j, x k) (x, t)) ∧
      c.cost = 2 ^ m * ((p - 1) - (p - 1) /
        leastAdmissibleOrder (p - 1) (m + 1) (by omega) (by omega)) +
          ∑ j : Fin m, (2 + 2 ^ j.val) * q j := by
  choose power hpower hpowerCost _hpowerLocal using
    (fun (a : ZMod p) => indexed_power first target hfirst a (m + 1) (by omega) (by omega))
  let calls := polarizationCircuit (n := m)
    (μ * (((2 : ZMod p) ^ m * ((m + 1).factorial : ZMod p))⁻¹))
  refine ⟨compilePolarization group power calls, ?_⟩
  exact compiled_grouped_polarization hp hdegree first target hfirst groups hgroups htarget
    group power q _ hgroup hpower hcost hpowerCost μ

end Toffoli
