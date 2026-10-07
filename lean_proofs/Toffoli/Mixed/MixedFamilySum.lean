import Toffoli.Mixed.FamilyProductConstructionModel

namespace Toffoli

/-- A singleton control compiles to the concrete SUM or internal shear
specified by the family, with zero transposition cost. -/
theorem mixed_family_sum {p : ℕ} [Fact p.Prime] (b : ℕ) :
    FamilyProductConstruction p 1 b 0 := by
  intro n controls pool hsubset hcard hpool target htarget μ
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
  have hi : i ∈ pool := hsubset (Finset.mem_singleton_self i)
  refine ⟨indexedSumCircuit i target (htarget i hi) μ,
    .sum b i pool hi hpool target htarget μ, ?_, ?_, ?_⟩
  · cases target with
    | none =>
      intro x t
      simp [indexedSumCircuit, MultiCircuit.eval, MultiGate.eval,
        MultiGate.control, MultiGate.increment, indexedTargetAdd]
    | some j =>
      intro x t
      simpa only [indexedSumCircuit, Finset.prod_singleton] using
        coordinate_shear_eval i j μ (by simpa [ne_comm] using htarget i hi) x t
  · cases target <;> rfl
  · refine ⟨htarget, ?_⟩
    cases target with
    | none =>
      exact List.forall_mem_singleton.mpr (AccumulatorGate.sum i hi μ)
    | some j =>
      exact List.forall_mem_singleton.mpr
        (AccumulatorGate.shear i j hi μ (by simpa [ne_comm] using htarget i hi))

end Toffoli
