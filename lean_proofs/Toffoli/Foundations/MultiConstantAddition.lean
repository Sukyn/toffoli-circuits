import Toffoli.Foundations.CoordinateLiftModel

namespace Toffoli

/-- A constant uses one available control, restored at the end:
subtract x_i, translate x_i by b, add x_i+b, then undo the translation. -/
theorem multi_constant_addition {K : Type*} [Field K] {n : ℕ}
    (i : Fin n) (b : K) :
    ∃ c : MultiCircuit K n, c.Realizes (fun _ => b) ∧ c.cost = 0 := by
  let e := coordinateAffine i 1 b one_ne_zero
  refine ⟨[MultiGate.sum i (-1), .affine e, .sum i 1, .affine e.symm], ?_, ?_⟩
  · intro x t
    simp only [MultiCircuit.eval, List.foldl_cons, List.foldl_nil, MultiGate.eval,
      MultiGate.control, MultiGate.increment, add_zero, Equiv.refl_apply,
      AffineEquiv.coe_toEquiv, AffineEquiv.symm_apply_apply]
    simp [e, coordinateAffine, smul_eq_mul, add_comm, add_left_comm, add_assoc]
  · simp [MultiCircuit.cost, MultiGate.cost]

end Toffoli
