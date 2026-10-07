import Toffoli.Polynomial.MultiGateZeroSum

namespace Toffoli

/-- The target table keeps its total sum through an arbitrary gate list.
The accumulated control permutation is tracked explicitly, so this includes
SUMs applied after entangling affine maps and local transpositions. -/
theorem multi_circuit_preserves_target_sum {K : Type*} [Field K] [Fintype K]
    (hcard : 2 < Fintype.card K) {n : ℕ} (c : MultiCircuit K n)
    (control : Equiv.Perm (Controls K n)) (target : Controls K n → K) :
    (∑ x, (c.eval (control x, target x)).2) = ∑ x, target x := by
  classical
  induction c generalizing control target with
  | nil => rfl
  | cons gate rest ih =>
    have hz : (∑ x, gate.increment (control x)) = 0 :=
      (Equiv.sum_comp control gate.increment).trans (multi_gate_zero_sum hcard gate)
    calc
      (∑ x, (MultiCircuit.eval (gate :: rest) (control x, target x)).2) =
          (∑ x, (target x + gate.increment (control x))) := by
        simpa only [MultiCircuit.eval, List.foldl_cons, MultiGate.eval, Equiv.trans_apply] using
          ih (control.trans gate.control) (fun x => target x + gate.increment (control x))
      _ = (∑ x, target x) := by rw [Finset.sum_add_distrib, hz, add_zero]

end Toffoli
