import Toffoli.Additions.OddBlocks

namespace Toffoli
variable {K : Type*} [Field K]

/-- Each negation pair uses exactly one transposition. -/
theorem odd_blocks_cost (f : K → K) (l : List K) :
    (oddBlocks f l).cost = l.length := by
  -- Add the one-transposition cost of each block in the list.
  rw [oddBlocks, Circuit.cost, List.map_flatMap, List.flatMap_def,
    List.sum_flatten, List.map_map]
  simp [Function.comp_def, cycleTransferBlock, List.map_const']

end Toffoli
