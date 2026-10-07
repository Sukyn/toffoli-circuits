import Toffoli.Foundations.MultiControlModel

namespace Toffoli

/-- Concatenated circuits execute the first circuit, then the second. -/
theorem multi_circuit_eval_append {K : Type*} [Field K] {n : ℕ}
    (c d : MultiCircuit K n) (state : Controls K n × K) :
    (c ++ d).eval state = d.eval (c.eval state) :=
  List.foldl_append

end Toffoli
