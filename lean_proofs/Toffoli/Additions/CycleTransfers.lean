import Toffoli.Additions.CycleTransferBlock

namespace Toffoli
variable {K : Type*} [Field K] [DecidableEq K]

/-- Star transfers in cycle order. The value at the anchor stores the running
prefix sum, so the successive amounts are -f(a), -(f(a)+f(b)), and so on. -/
noncomputable def cycleTransfers (a : K) : List K → (K → K) → Circuit K
  | [], _ => []
  | b :: rest, f => cycleTransferBlock a b (-f a) ++
      cycleTransfers a rest (Function.update f a (f a + f b))

end Toffoli
