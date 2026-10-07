import Toffoli.Mixed.FamilyProductConstructionModel
import Toffoli.Mixed.MixedPolarizationLayout
import Toffoli.Polarization.CompiledGroupedPolarization
import Toffoli.Additions.IndexedPowerCircuitFamilyAttains
import Toffoli.Foundations.CircuitLocalityPromote
import Toffoli.Foundations.CircuitLocalityMono
import Toffoli.Foundations.CircuitLocalityList
import Toffoli.Divide.DivideLayoutProduct
import Mathlib.Tactic.Choose

namespace Toffoli

/-- Compile polarization while retaining one family derivation for each
primitive chunk. Uniform choices attain the weighted count, although the
family also permits different implementations of repeated calls. -/
theorem mixed_family_polarization {p d b : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hd : 2 ≤ d) (c : Composition (d - 1)) (hdegree : c.length + 1 ≤ p - 2)
    (q : Fin c.length → ℕ)
    (children : ∀ j, FamilyProductConstruction p (c.blocksFun j)
      (d + b - c.blocksFun j - 1) (q j)) :
    FamilyProductConstruction p d b (divideStepCost p c hdegree q) := by
  classical
  intro n controls pool hsubset hcard hpool target htarget μ
  obtain ⟨first, hfirst, groups, hcards, hchildSubset, hdisjoint, hcover, hbudget⟩ :=
    mixed_polarization_layout pool controls hsubset hcard hpool (by omega) c
  let layout : MixedPolarizationLayout (b := b) c controls pool :=
    ⟨hsubset, hcard, hpool, first, hfirst, groups, hcards, hchildSubset,
      hdisjoint, hcover⟩
  have hfirstPool : first ∈ pool := hsubset hfirst
  have hchildTarget : ∀ i ∈ pool.erase first, (some first : IndexedTarget n) ≠ some i := by
    intro i hi
    simpa only [ne_eq, Option.some.injEq] using (Finset.mem_erase.mp hi).1.symm
  choose group hfamily hgroup hcost hlocal using
    (fun j (a : ZMod p) => children j (groups j) (pool.erase first)
      (hchildSubset j) (hcards j) (hbudget j).1 (some first) hchildTarget a)
  choose power hpowerFamily hpower hpowerCost hpowerLocal using
    (fun a : ZMod p => indexed_power_circuit_family_attains first target
      (htarget first hfirstPool) a (c.length + 1) (by omega) (by omega))
  have hfirstNot (j : Fin c.length) : first ∉ groups j :=
    (Finset.subset_erase.mp (hchildSubset j)).2
  have hgroupSubset (j : Fin c.length) : groups j ⊆ pool :=
    (Finset.subset_erase.mp (hchildSubset j)).1
  have hparentLocal (j : Fin c.length) (a : ZMod p) :
      (group j a).AccumulatorLocal pool target :=
    circuit_locality_promote (group j a) (pool.erase first) pool
      (Finset.erase_subset first pool) first hfirstPool target htarget (hlocal j a)
  let calls := polarizationCircuit (n := c.length)
    (μ * (((2 : ZMod p) ^ c.length * ((c.length + 1).factorial : ZMod p))⁻¹))
  let chunks (r : Fin calls.length) := PolarizationCall.compile group power (calls.get r)
  have hflat : (List.ofFn chunks).flatten = compilePolarization group power calls := by
    simp only [chunks, List.ofFn_comp', List.ofFn_get, compilePolarization, List.flatMap_def]
  have member : MixedCircuitFamily d b controls pool target μ (List.ofFn chunks).flatten := by
    apply MixedCircuitFamily.polarization hd c hdegree layout target htarget μ calls rfl chunks
    · intro r j a hr
      simpa only [chunks, hr, PolarizationCall.compile] using hfamily j a
    · intro r a hr
      simpa only [chunks, hr, PolarizationCall.compile] using hpowerFamily a
  rw [hflat] at member
  obtain ⟨hrun, hcount⟩ := compiled_grouped_polarization hp hdegree first target
    (htarget first hfirstPool) groups hfirstNot
    (fun j k hk => htarget k (hgroupSubset j hk)) group power q _
    (by simpa only [indexedTargetAdd] using hgroup) hpower hcost hpowerCost μ
  refine ⟨compilePolarization group power calls, member, ?_, hcount, ?_⟩
  · intro x t
    have hproduct := divide_layout_product controls hfirst groups hdisjoint hcover x
    simpa only [mul_assoc, hproduct] using hrun x t
  · apply circuit_locality_list calls (PolarizationCall.compile group power) pool target htarget
    intro call _
    cases call with
    | group j a => exact hparentLocal j a
    | power a =>
      exact circuit_locality_mono (hpowerLocal a) (Finset.singleton_subset_iff.mpr hfirstPool) htarget

end Toffoli
