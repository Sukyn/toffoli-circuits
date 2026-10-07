import Toffoli.Foundations.AffineLocalMono
import Toffoli.Foundations.CoordinateShearLocality

namespace Toffoli

/-- An internal child's gates are control gates for its parent. The child's
SUM becomes an affine shear within the larger pool; no excluded wire is
read or changed. The parent's target exclusion is recorded by circuit locality. -/
theorem accumulator_gate_promote {K : Type*} [Field K] {n : ℕ}
    (childPool parentPool : Finset (Fin n)) (hpool : childPool ⊆ parentPool)
    (childTarget : Fin n) (hchild : childTarget ∈ parentPool)
    (parentTarget : IndexedTarget n) {gate : MultiGate K n}
    (hgate : AccumulatorGate childPool (some childTarget) gate) :
    AccumulatorGate parentPool parentTarget gate := by
  cases hgate with
  | affine _ e hlocal =>
    exact AccumulatorGate.affine parentTarget e (affine_local_mono hlocal hpool)
  | swap _ i hi a b =>
    exact AccumulatorGate.swap parentTarget i (hpool hi) a b
  | shear source _ hsource coefficient hne =>
    apply AccumulatorGate.affine parentTarget
    apply affine_local_mono (coordinate_shear_locality source childTarget coefficient hne)
    -- Both the shear's source and its destination belong to the parent's pool.
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
      And.intro (hpool hsource) hchild

end Toffoli
