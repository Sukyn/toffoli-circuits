import Toffoli.Foundations.CoordinateAffineLocality

namespace Toffoli

/-- A coordinate lift reads only its selected control. The external target
is used solely as a SUM destination, even at intermediate gate boundaries. -/
theorem coordinate_lift_locality {K : Type*} [Field K] {n : ℕ}
    (c : Circuit K) (i : Fin n) :
    (c.lift i).AccumulatorLocal {i} none := by
  refine ⟨by simp, ?_⟩
  intro gate hgate
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp hgate
  cases g with
  | affine a b ha =>
    exact AccumulatorGate.affine none _ (coordinate_affine_locality i a b ha)
  | swap a b =>
    exact AccumulatorGate.swap none i (Finset.mem_singleton_self i) a b
  | sum coefficient =>
    exact AccumulatorGate.sum i (Finset.mem_singleton_self i) coefficient

end Toffoli
