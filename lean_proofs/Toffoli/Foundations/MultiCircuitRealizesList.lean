import Toffoli.Foundations.MultiCircuitRealizesAppend

namespace Toffoli

/-- Flattening a list of restored circuits adds all their increments. -/
theorem multi_circuit_realizes_list {K I : Type*} [Field K] {n : ℕ}
    (l : List I) (c : I → MultiCircuit K n) (f : I → Controls K n → K)
    (hc : ∀ a ∈ l, (c a).Realizes (f a)) :
    MultiCircuit.Realizes (l.flatMap c) (fun x => (l.map (fun a => f a x)).sum) := by
  induction l with
  | nil => simp [MultiCircuit.Realizes, MultiCircuit.eval]
  | cons a l ih =>
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
    exact multi_circuit_realizes_append _ _ _ _ (hc a (by simp))
      (ih (fun b hb => hc b (by simp [hb])))

end Toffoli
