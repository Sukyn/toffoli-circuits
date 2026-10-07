import Toffoli.Polarization.IndexedPolarizationExecution
import Toffoli.Polarization.IndexedPolarizationCost
import Toffoli.Polarization.ScaledGroupedPolarization

namespace Toffoli

/-- The compiled Gray trace adds the grouped product with the exact weighted
cost. Later locality proofs apply to this same gate list. -/
theorem compiled_grouped_polarization {p m n : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hdegree : m + 1 ≤ p - 2)
    (first : Fin n) (target : IndexedTarget n) (hfirst : target ≠ some first)
    (groups : Fin m → Finset (Fin n))
    (hgroups : ∀ j, first ∉ groups j)
    (htarget : ∀ j, ∀ k ∈ groups j, target ≠ some k)
    (group : Fin m → ZMod p → MultiCircuit (ZMod p) n)
    (power : ZMod p → MultiCircuit (ZMod p) n) (q : Fin m → ℕ) (r : ℕ)
    (hgroup : ∀ j a x t, (group j a).eval (x, t) =
      (Function.update x first (x first + a * ∏ k ∈ groups j, x k), t))
    (hpower : ∀ a x t, (power a).eval (x, t) =
      indexedTargetAdd target (a * x first ^ (m + 1)) (x, t))
    (hcost : ∀ j a, (group j a).cost = q j)
    (hpowerCost : ∀ a, (power a).cost = r) (μ : ZMod p) :
    let calls := polarizationCircuit (n := m)
      (μ * (((2 : ZMod p) ^ m * ((m + 1).factorial : ZMod p))⁻¹))
    (∀ x t, (compilePolarization group power calls).eval (x, t) =
      indexedTargetAdd target (μ * x first * ∏ j, ∏ k ∈ groups j, x k) (x, t)) ∧
    (compilePolarization group power calls).cost =
      2 ^ m * r + ∑ j : Fin m, (2 + 2 ^ j.val) * q j := by
  let normalization := μ * (((2 : ZMod p) ^ m * ((m + 1).factorial : ZMod p))⁻¹)
  let calls := polarizationCircuit (n := m) normalization
  constructor
  · intro x t
    -- Embed the two macro registers in their original wire positions.
    have hstart : polarizationState first target x t
        (x first, indexedTargetValue target x t) = (x, t) := by
      cases target <;> simp [polarizationState, indexedTargetValue]
    have hexecution := indexed_polarization_execution first target hfirst groups
      hgroups htarget group power hgroup hpower calls x t
        (x first, indexedTargetValue target x t)
    rw [hstart] at hexecution
    have hrun := (scaled_grouped_polarization hp m hdegree
      (fun j => ∏ k ∈ groups j, x k) μ (x first) (indexedTargetValue target x t)).1
    change runPolarization _ calls _ = _ at hrun
    rw [hexecution, hrun]
    cases target <;> simp [polarizationState, indexedTargetValue, indexedTargetAdd]
  · -- Each power call costs r; each call to group j costs q j.
    change (compilePolarization group power calls).cost = _
    rw [indexed_polarization_cost group power q r hcost hpowerCost]
    obtain ⟨hpowerCalls, hgroupCalls⟩ :=
      polarization_circuit_calls (n := m) normalization
    simp only [calls, hpowerCalls, hgroupCalls]

end Toffoli
