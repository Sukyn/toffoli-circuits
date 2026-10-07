import Toffoli.Foundations.IndexedTargetModel

namespace Toffoli

/-- Undo a workspace update after updating a different destination. The
target increment remains, and the borrowed control returns to its old value. -/
theorem indexed_target_restore {K : Type*} [AddGroup K] {n : ℕ}
    (target : IndexedTarget n) (i : Fin n) (hti : target ≠ some i)
    (a b : K) (state : Controls K n × K) :
    indexedTargetAdd (some i) (-a)
      (indexedTargetAdd target b (indexedTargetAdd (some i) a state)) =
        indexedTargetAdd target b state := by
  cases target with
  | none => simp [indexedTargetAdd]
  | some j =>
    have hji : j ≠ i := by simpa using hti
    simp [indexedTargetAdd, hji, hji.symm, Function.update_comm hji]

end Toffoli
