import Toffoli.Polarization.CompiledGroupedPolarization
import Toffoli.Additions.IndexedPower
import Toffoli.Foundations.CircuitLocalityMono
import Toffoli.Foundations.CircuitLocalityList
import Mathlib.Tactic.Choose

namespace Toffoli

/-- Grouped polarization preserves protected wires at every primitive gate.
Preparations have already been promoted to the parent pool; the power calls
read only the reserved control and use the parent target only as a destination. -/
theorem indexed_grouped_polarization_local {p m n : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hdegree : m + 1 ≤ p - 2)
    (pool : Finset (Fin n)) (first : Fin n) (hfirst : first ∈ pool)
    (target : IndexedTarget n) (htarget : ∀ i ∈ pool, target ≠ some i)
    (groups : Fin m → Finset (Fin n))
    (hgroups : ∀ j, first ∉ groups j) (hsubset : ∀ j, groups j ⊆ pool)
    (group : Fin m → ZMod p → MultiCircuit (ZMod p) n) (q : Fin m → ℕ)
    (hgroup : ∀ j a x t, (group j a).eval (x, t) =
      (Function.update x first (x first + a * ∏ k ∈ groups j, x k), t))
    (hcost : ∀ j a, (group j a).cost = q j)
    (hlocal : ∀ j a, (group j a).AccumulatorLocal pool target) (μ : ZMod p) :
    ∃ c : MultiCircuit (ZMod p) n,
      (∀ x t, c.eval (x, t) = indexedTargetAdd target
        (μ * x first * ∏ j, ∏ k ∈ groups j, x k) (x, t)) ∧
      c.cost = 2 ^ m * ((p - 1) - (p - 1) /
        leastAdmissibleOrder (p - 1) (m + 1) (by omega) (by omega)) +
          ∑ j : Fin m, (2 + 2 ^ j.val) * q j ∧
      c.AccumulatorLocal pool target := by
  choose power hpower hpowerCost hpowerLocal using
    (fun (a : ZMod p) => indexed_power first target (htarget first hfirst)
      a (m + 1) (by omega) (by omega))
  let calls := polarizationCircuit (n := m)
    (μ * (((2 : ZMod p) ^ m * ((m + 1).factorial : ZMod p))⁻¹))
  obtain ⟨hrun, hcount⟩ := compiled_grouped_polarization hp hdegree first target
    (htarget first hfirst) groups hgroups (fun j k hk => htarget k (hsubset j hk))
    group power q _ hgroup hpower hcost hpowerCost μ
  refine ⟨compilePolarization group power calls, hrun, hcount, ?_⟩
  apply circuit_locality_list calls (PolarizationCall.compile group power) pool target htarget
  intro call _
  cases call with
  | group j a => exact hlocal j a
  | power a =>
    exact circuit_locality_mono (hpowerLocal a) (Finset.singleton_subset_iff.mpr hfirst) htarget

end Toffoli
