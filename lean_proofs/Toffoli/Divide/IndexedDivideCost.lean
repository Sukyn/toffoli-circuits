import Toffoli.Divide.DivideModel
import Toffoli.Divide.DivideLayout
import Toffoli.Divide.DivideLayoutProduct
import Toffoli.Polarization.IndexedGroupedPolarizationLocal
import Toffoli.Foundations.IndexedSum
import Toffoli.Foundations.CircuitLocalityPromote

namespace Toffoli

/-- Compile a divide cost tree using only its control pool and accumulator.
Each preparation is local on its own group; promoting that certificate to
the parent pool protects every excluded wire throughout the construction. -/
theorem indexed_divide_cost {p d cost : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (tree : DivideCost p d cost) :
    ∀ {n : ℕ} (controls : Finset (Fin n)), controls.card = d →
      ∀ (target : IndexedTarget n), (∀ i ∈ controls, target ≠ some i) →
        ∀ μ : ZMod p, ∃ circuit : MultiCircuit (ZMod p) n,
          (∀ x t, circuit.eval (x, t) =
            indexedTargetAdd target (μ * ∏ i ∈ controls, x i) (x, t)) ∧
          circuit.cost = cost ∧ circuit.AccumulatorLocal controls target := by
  classical
  induction tree with
  | sum =>
    intro n controls hcard target htarget μ
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
    obtain ⟨circuit, hrun, hcost, hlocal⟩ :=
      indexed_sum i target (htarget i (by simp)) μ
    exact ⟨circuit, by simpa using hrun, hcost, hlocal⟩
  | @step d hd c hdegree q _children ih =>
    intro n controls hcard target htarget μ
    subst d
    -- Reserve one control and partition the rest on their original indices.
    obtain ⟨first, hfirst, groups, hcards, hfirstNot, hsubset, hdisjoint, hcover⟩ :=
      divide_layout controls (Finset.card_pos.mp (by omega)) c
    -- Each recursive call prepares its group into the reserved wire.
    choose group hgroup hcost hlocal using
      (fun j (a : ZMod p) => ih j (groups j) (hcards j) (some first)
        (by
          simpa only [ne_eq, Option.some.injEq, Finset.forall_mem_not_eq]
            using hfirstNot j) a)
    have hparentLocal (j : Fin c.length) (a : ZMod p) :
        (group j a).AccumulatorLocal controls target :=
      circuit_locality_promote (group j a) (groups j) controls (hsubset j)
        first hfirst target htarget (hlocal j a)
    obtain ⟨circuit, hrun, hcount, hprotected⟩ := indexed_grouped_polarization_local
      hp hdegree controls first hfirst target htarget groups hfirstNot hsubset group q
      (by simpa only [indexedTargetAdd] using hgroup) hcost hparentLocal μ
    refine ⟨circuit, ?_, hcount, hprotected⟩
    -- Disjointness and coverage recombine the groups into the original product.
    intro x t
    have hproduct := divide_layout_product controls hfirst groups hdisjoint hcover x
    simpa only [mul_assoc, hproduct] using hrun x t

end Toffoli
