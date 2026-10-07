import Toffoli.Foundations.CoordinateAffineLocality
import Toffoli.Foundations.InternalLiftModel

namespace Toffoli

/-- An internal lift reads only its source and adds only into its selected
target. The external target and all other wires are excluded gate by gate. -/
theorem internal_lift_locality {K : Type*} [Field K] {n : ℕ}
    (c : Circuit K) (i j : Fin n) (hij : i ≠ j) :
    (c.internalLift i j hij).AccumulatorLocal {i} (some j) := by
  refine ⟨by simp [hij.symm], ?_⟩
  intro gate hgate
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp hgate
  cases g with
  | affine a b ha =>
    exact AccumulatorGate.affine (some j) _ (coordinate_affine_locality i a b ha)
  | swap a b =>
    exact AccumulatorGate.swap (some j) i (Finset.mem_singleton_self i) a b
  | sum coefficient =>
    exact AccumulatorGate.shear i j (Finset.mem_singleton_self i) coefficient hij

end Toffoli
