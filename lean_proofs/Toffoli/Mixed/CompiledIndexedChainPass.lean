import Toffoli.Mixed.IndexedGroupedPassStep
import Toffoli.Mixed.IndexedLadderTraceModel
import Toffoli.Borrow.BorrowedLadderModel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

namespace Toffoli

/-- Compile the recorded signed pass itself. A middle stage updates the next
dirty wire and is undone after the tail; the last stage updates the parent
target. Execution, cost, and locality refer to this same primitive list. -/
theorem compiled_indexed_chain_pass {K : Type*} [Field K] {n m : ℕ}
    (pool : Finset (Fin n)) (target : IndexedTarget n)
    (factors : Fin (m + 1) → Finset (Fin n)) (dirty : Fin (m + 1) → Fin n)
    (hdirty : Function.Injective dirty)
    (houtside : ∀ i j, dirty i ∉ factors j)
    (htdirty : ∀ i, target ≠ some (dirty i))
    (htfactors : ∀ j, ∀ i ∈ factors j, target ≠ some i)
    (call : Fin (m + 1) → K → MultiCircuit K n)
    (q : Fin (m + 1) → ℕ)
    (hprepare : ∀ (j : Fin m) a x t, (call j.castSucc a).eval (x, t) =
      indexedTargetAdd (some (dirty j.succ))
        (a * x (dirty j.castSucc) * ∏ i ∈ factors j.castSucc, x i) (x, t))
    (hfinish : ∀ a x t, (call (Fin.last m) a).eval (x, t) = indexedTargetAdd target
      (a * x (dirty (Fin.last m)) * ∏ i ∈ factors (Fin.last m), x i) (x, t))
    (hcost : ∀ j a, (call j a).cost = q j)
    (hlocal : ∀ j a, (call j a).AccumulatorLocal pool target) (μ : K) :
    let circuit : MultiCircuit K n := (indexedPassTrace m μ).flatMap (fun step => call step.1 step.2)
    (∀ x t, circuit.eval (x, t) = indexedTargetAdd target
        (μ * borrowedPropagation (x (dirty 0))
          (List.ofFn (fun j : Fin m =>
            ((∏ i ∈ factors j.castSucc, x i), x (dirty j.succ)))) *
          ∏ i ∈ factors (Fin.last m), x i) (x, t)) ∧
      circuit.cost = 2 * (∑ j : Fin m, q j.castSucc) + q (Fin.last m) ∧
      circuit.AccumulatorLocal pool target := by
  induction m with
  | zero =>
    simpa [indexedPassTrace, borrowedPropagation] using
      And.intro (hfinish μ) (And.intro (hcost 0 μ) (hlocal 0 μ))
  | succ m ih =>
    -- Removing the first position leaves the same finish circuit.
    obtain ⟨hbody, hbodyCost, hbodyLocal⟩ := ih
      (factors := fun j => factors j.succ) (dirty := fun j => dirty j.succ)
      (hdirty := fun _ _ h => Fin.succ_inj.mp (hdirty h))
      (houtside := fun i j => houtside i.succ j.succ)
      (htdirty := fun i => htdirty i.succ)
      (htfactors := fun j => htfactors j.succ)
      (call := fun j => call j.succ) (q := fun j => q j.succ)
      (hprepare := by
        intro j a x t
        simpa only [Fin.castSucc_succ] using hprepare j.succ a x t)
      (hfinish := by
        intro a x t
        simpa only [Fin.succ_last] using hfinish a x t)
      (hcost := fun j => hcost j.succ)
      (hlocal := fun j => hlocal j.succ)
    let body := (indexedPassTrace m μ).flatMap (fun step => call step.1.succ step.2)
    let values (x : Controls K n) := List.ofFn (fun j : Fin m =>
      ((∏ i ∈ factors j.castSucc.succ, x i), x (dirty j.succ.succ)))
    let tailCost := 2 * (∑ j : Fin m, q j.castSucc.succ) + q (Fin.last (m + 1))
    have hdirtyInputs : dirty (Fin.succ 0) ∉ insert (dirty 0) (factors 0) := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨hdirty.ne (Fin.succ_ne_zero _), houtside (Fin.succ 0) 0⟩
    have htargetInputs : ∀ i ∈ insert (dirty 0) (factors 0), target ≠ some i := by
      intro i hi
      rcases Finset.mem_insert.mp hi with hi | hi
      · subst i
        exact htdirty 0
      · exact htfactors 0 i hi
    obtain ⟨hrun, hstepCost, hstepLocal⟩ :=
      indexed_grouped_pass_step pool (insert (dirty 0) (factors 0))
        (dirty (Fin.succ 0)) target hdirtyInputs (htdirty (Fin.succ 0)) htargetInputs
        (call 0 1) body (call 0 (-1))
        (fun x => μ * borrowedPropagation (x (dirty (Fin.succ 0))) (values x) *
          ∏ i ∈ factors (Fin.last (m + 1)), x i) (q 0) tailCost
        (by
          simpa only [one_mul, Fin.castSucc_zero, Finset.prod_insert (houtside 0 0)]
            using hprepare 0 1)
        hbody
        (by
          simpa only [neg_one_mul, neg_mul, one_mul, Fin.castSucc_zero,
            Finset.prod_insert (houtside 0 0)] using hprepare 0 (-1))
        (hcost 0 1) hbodyCost (hcost 0 (-1))
        (hlocal 0 1) hbodyLocal (hlocal 0 (-1))
    -- The new source is absent from all later factors and dirty destinations.
    have hvalues (x : Controls K n) (v : K) :
        values (Function.update x (dirty (Fin.succ 0)) v) = values x := by
      dsimp only [values]
      apply congrArg List.ofFn
      funext j
      apply Prod.ext
      · exact Finset.prod_update_of_notMem (houtside (Fin.succ 0) j.castSucc.succ) x v
      · apply Function.update_of_ne
        intro h
        exact Fin.succ_ne_zero j (Fin.succ_inj.mp (hdirty h))
    have hlastUpdate (x : Controls K n) (v : K) :=
      Finset.prod_update_of_notMem (houtside (Fin.succ 0) (Fin.last (m + 1))) x v
    have htrace :
        (indexedPassTrace (m + 1) μ).flatMap (fun step => call step.1 step.2) =
          (call 0 1 ++ body) ++ call 0 (-1) := by
      simp [indexedPassTrace, body, List.flatMap_map, List.append_assoc]
    rw [htrace]
    refine ⟨?_, ?_, hstepLocal⟩
    · intro x t
      have h := hrun x t
      simp only [Function.update_self, hvalues, hlastUpdate,
        Finset.prod_insert (houtside 0 0)] at h
      simpa only [List.ofFn_succ, Fin.castSucc_zero, Fin.castSucc_succ,
        borrowedPropagation, values] using h
    · rw [hstepCost]
      simp only [Fin.sum_univ_succ, Fin.castSucc_zero, Fin.castSucc_succ]
      dsimp only [tailCost]
      ring

end Toffoli
