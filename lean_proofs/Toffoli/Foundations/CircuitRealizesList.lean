import Toffoli.Foundations.CircuitRealizesAppend

namespace Toffoli
variable {K ι : Type*} [Field K]

/-- A list of restored accumulator circuits realizes the sum of its increments. -/
theorem circuit_realizes_list (l : List ι) (c : ι → Circuit K) (f : ι → K → K)
    (hc : ∀ a ∈ l, (c a).Realizes (f a)) :
    Circuit.Realizes (l.flatMap c) (fun x => (l.map (fun a => f a x)).sum) := by
  induction l with
  | nil => simp [Circuit.Realizes, Circuit.eval]
  | cons a l ih =>
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
    exact circuit_realizes_append _ _ _ _ (hc a (by simp))
      (ih (fun b hb => hc b (by simp [hb])))

end Toffoli
