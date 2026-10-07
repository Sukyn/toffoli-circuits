import Toffoli.Foundations.AccumulatorLocalityModel

namespace Toffoli

/-- Concatenating local subcircuits preserves the same pool and target.
Every primitive gate belongs to one of the supplied subcircuits. -/
theorem circuit_locality_list {K ι : Type*} [Field K] {n : ℕ}
    (calls : List ι) (circuits : ι → MultiCircuit K n)
    (pool : Finset (Fin n)) (target : IndexedTarget n)
    (htarget : ∀ i ∈ pool, target ≠ some i)
    (hlocal : ∀ call ∈ calls, (circuits call).AccumulatorLocal pool target) :
    MultiCircuit.AccumulatorLocal (calls.flatMap circuits) pool target := by
  refine ⟨htarget, List.forall_mem_flatMap.mpr ?_⟩
  intro call hcall
  exact (hlocal call hcall).gates

end Toffoli
