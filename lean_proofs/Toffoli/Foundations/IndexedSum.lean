import Toffoli.Foundations.AccumulatorLocalityModel
import Toffoli.Foundations.CoordinateShearEval

namespace Toffoli

/-- A SUM or coordinate shear reads its single source and adds into the
selected target. This one-gate witness has zero transposition cost. -/
theorem indexed_sum {K : Type*} [Field K] {n : ℕ}
    (i : Fin n) (target : IndexedTarget n) (hti : target ≠ some i) (μ : K) :
    ∃ c : MultiCircuit K n,
      (∀ x t, c.eval (x, t) = indexedTargetAdd target (μ * x i) (x, t)) ∧
      c.cost = 0 ∧ c.AccumulatorLocal {i} target := by
  cases target with
  | none =>
    refine ⟨[MultiGate.sum i μ], ?_, rfl, ?_⟩
    · intro x t
      simp [MultiCircuit.eval, MultiGate.eval, MultiGate.control,
        MultiGate.increment, indexedTargetAdd]
    · refine ⟨by simp, ?_⟩
      exact List.forall_mem_singleton.mpr
        (AccumulatorGate.sum i (Finset.mem_singleton_self i) μ)
  | some j =>
    have hji : j ≠ i := by simpa using hti
    refine ⟨[MultiGate.affine (coordinateShear i j μ hji.symm)], ?_, rfl, ?_⟩
    · intro x t
      exact coordinate_shear_eval i j μ hji.symm x t
    · refine ⟨by simp [hji], ?_⟩
      exact List.forall_mem_singleton.mpr
        (AccumulatorGate.shear i j (Finset.mem_singleton_self i) μ hji.symm)

end Toffoli
