import Toffoli.Foundations.Basic

namespace Toffoli
variable {K : Type*} [Field K]

/-- Restored controls let successive accumulator increments add. -/
theorem circuit_realizes_append (c d : Circuit K) (f g : K → K)
    (hc : c.Realizes f) (hd : d.Realizes g) :
    (c ++ d).Realizes (fun x => f x + g x) := by
  intro x t
  simp only [Circuit.eval, List.foldl_append]
  change d.eval (c.eval (x, t)) = _
  rw [hc x t, hd x (t + f x)]
  simp [add_assoc]

end Toffoli
