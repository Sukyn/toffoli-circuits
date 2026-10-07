import Toffoli.Mixed.MixedCircuitFamilyModel
import Toffoli.Mixed.MixedPolarizationBound
import Toffoli.Additions.IndexedPowerCircuitFamilyLower
import Toffoli.Polarization.PolarizationTraceNonzero
import Toffoli.Polarization.PolarizationOccurrenceCost
import Toffoli.Mixed.IndexedLadderOccurrenceCost
import Toffoli.Mixed.IndexedLadderTraceNonzero
import Mathlib.Data.List.OfFn

namespace Toffoli

/-- Every circuit in the recursive family pays at least the recurrence.
The induction applies separately to each occurrence, including undo calls;
the power leaves may choose any admissible affine-return cycle algorithm. -/
theorem mixed_circuit_family_lower {p n d b : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {controls pool : Finset (Fin n)} {target : IndexedTarget n} {μ : ZMod p}
    {circuit : MultiCircuit (ZMod p) n}
    (member : MixedCircuitFamily d b controls pool target μ circuit) (hμ : μ ≠ 0) :
    mixedCount p hp d b ≤ circuit.cost := by
  classical
  revert hμ
  induction member with
  | sum =>
    intro _
    rw [mixed_count_one]
    exact Nat.zero_le _
  | @polarization d b hd c hdegree controls pool layout target htarget μ calls
      htrace chunks _groups powers ih =>
    intro hμ
    let q := fun j => mixedCount p hp (c.blocksFun j) (d + b - c.blocksFun j - 1)
    let powerCost := (p - 1) - (p - 1) /
      leastAdmissibleOrder (p - 1) (c.length + 1) (by omega) (by omega)
    have hcost (r : Fin calls.length) :
        PolarizationCall.weight q powerCost (calls.get r) ≤ (chunks r).cost := by
      have hnonzero : (calls.get r).coefficient ≠ 0 :=
        polarization_trace_nonzero hp hdegree hμ (by
          rw [← htrace]
          exact List.get_mem calls r)
      cases hcall : calls.get r with
      | group j a =>
        exact ih r j a hcall
          (by simpa only [hcall, PolarizationCall.coefficient] using hnonzero)
      | power a =>
        exact indexed_power_circuit_family_lower (powers r a hcall)
          (by simpa only [hcall, PolarizationCall.coefficient] using hnonzero)
          (by omega) (by omega)
    have hlist : List.Forall₂
        (fun call (chunk : MultiCircuit (ZMod p) n) =>
          PolarizationCall.weight q powerCost call ≤ chunk.cost)
        calls (List.ofFn chunks) := by
      apply List.forall₂_of_length_eq_of_get (by simp)
      intro i hi hi'
      simpa using hcost ⟨i, hi⟩
    have hbound := polarization_occurrence_cost
      (μ * (((2 : ZMod p) ^ c.length * ((c.length + 1).factorial : ZMod p))⁻¹))
      q powerCost (List.ofFn chunks) (by simpa only [← htrace] using hlist)
    exact (mixed_polarization_bound hp hd b c hdegree).trans hbound
  | @ladder d b hd L controls pool layout target htarget μ m hlength chunks _children ih =>
    intro hμ
    let index : Fin (m + 2) ≃ Fin L.groups.length := finCongr hlength.symm
    let q := fun j => mixedCount p hp (L.controls j) (L.borrowed j)
    let calls := indexedLadderTrace m μ
    have hindex (j : Fin (m + 2)) : (index j).val = j.val := rfl
    have hcost (r : Fin calls.length) : q (index (calls.get r).1) ≤ (chunks r).cost := by
      exact ih r (indexed_ladder_trace_nonzero hμ (List.get_mem calls r))
    have hbound := indexed_ladder_occurrence_cost μ (fun j => q (index j)) chunks hcost
    have hsum : (∑ j : Fin (m + 2),
        (if j.val = 0 ∨ j.val + 1 = m + 2 then 2 else 4) * q (index j)) = L.cost q := by
      simpa only [MixedLadder.cost, hindex, hlength] using
        index.sum_comp (fun j =>
          (if j.val = 0 ∨ j.val + 1 = L.groups.length then 2 else 4) * q j)
    rw [hsum] at hbound
    exact ((mixed_recurrence hp hd b).2 (Or.inr ⟨L, rfl⟩)).trans hbound

end Toffoli
