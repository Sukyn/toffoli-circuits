import Toffoli.Foundations.AccumulatorLocalityModel
import Toffoli.Foundations.IndexedTargetControl
import Toffoli.Foundations.IndexedTargetRestore
import Toffoli.Foundations.MultiCircuitCostAppend
import Toffoli.Foundations.MultiCircuitEvalAppend
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Toffoli

/-- One recursive pass step prepares a group product into a dirty wire,
runs the supplied primitive tail, then restores the dirty wire. The tail's
increment is evaluated on the prepared register. All three circuits have
already been certified local in the parent's pool. -/
theorem indexed_grouped_pass_step {K : Type*} [Field K] {n : ℕ}
    (pool inputs : Finset (Fin n)) (dirty : Fin n) (target : IndexedTarget n)
    (hdirty : dirty ∉ inputs) (htdirty : target ≠ some dirty)
    (htinputs : ∀ i ∈ inputs, target ≠ some i)
    (prepare body undo : MultiCircuit K n) (value : Controls K n → K) (q r : ℕ)
    (hprepare : ∀ x t, prepare.eval (x, t) =
      indexedTargetAdd (some dirty) (∏ i ∈ inputs, x i) (x, t))
    (hbody : ∀ x t, body.eval (x, t) = indexedTargetAdd target (value x) (x, t))
    (hundo : ∀ x t, undo.eval (x, t) =
      indexedTargetAdd (some dirty) (-(∏ i ∈ inputs, x i)) (x, t))
    (hprepareCost : prepare.cost = q) (hbodyCost : body.cost = r)
    (hundoCost : undo.cost = q)
    (hprepareLocal : prepare.AccumulatorLocal pool target)
    (hbodyLocal : body.AccumulatorLocal pool target)
    (hundoLocal : undo.AccumulatorLocal pool target) :
    (∀ x t, ((prepare ++ body) ++ undo).eval (x, t) =
      indexedTargetAdd target
        (value (Function.update x dirty (x dirty + ∏ i ∈ inputs, x i))) (x, t)) ∧
    ((prepare ++ body) ++ undo).cost = 2 * q + r ∧
    ((prepare ++ body) ++ undo).AccumulatorLocal pool target := by
  have hproductUpdate (x : Controls K n) (v : K) :=
    Finset.prod_update_of_notMem hdirty x v
  have hproductTarget (x : Controls K n) (t amount : K) :
      (∏ i ∈ inputs, (indexedTargetAdd target amount (x, t)).1 i) =
        ∏ i ∈ inputs, x i :=
    Finset.prod_congr rfl (fun i hi =>
      indexed_target_add_control target amount x t i (htinputs i hi))
  refine ⟨?_, ?_, ?_⟩
  · intro x t
    rw [multi_circuit_eval_append, multi_circuit_eval_append, hprepare]
    change undo.eval (body.eval
      (Function.update x dirty (x dirty + ∏ i ∈ inputs, x i), t)) = _
    rw [hbody, hundo]
    -- Neither the preparation nor the tail changes the preparation's inputs.
    simp only [hproductTarget, hproductUpdate]
    exact indexed_target_restore target dirty htdirty (∏ i ∈ inputs, x i)
      (value (Function.update x dirty (x dirty + ∏ i ∈ inputs, x i))) (x, t)
  · rw [multi_circuit_cost_append, multi_circuit_cost_append,
      hprepareCost, hbodyCost, hundoCost]
    ring
  · exact ⟨hprepareLocal.target_outside, List.forall_mem_append.mpr
      ⟨List.forall_mem_append.mpr ⟨hprepareLocal.gates, hbodyLocal.gates⟩,
        hundoLocal.gates⟩⟩

end Toffoli
