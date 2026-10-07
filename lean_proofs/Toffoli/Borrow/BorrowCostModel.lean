import Toffoli.Borrow.BinaryLadderCostModel

namespace Toffoli

/-- The paper's Borrow count: a SUM for one control, one Toffoli for two,
then three preparations of F, four of yH, and four target Toffolis. -/
def borrowCost (C2 d : ℕ) : ℕ :=
  if d ≤ 2 then binaryLadderCost C2 d else
    3 * binaryLadderCost C2 ((d + 1) / 2) +
      4 * binaryLadderCost C2 (d / 2) + 4 * C2

end Toffoli
