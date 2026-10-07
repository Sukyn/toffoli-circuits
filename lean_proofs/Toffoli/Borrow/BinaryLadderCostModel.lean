import Mathlib.Data.Nat.Basic

namespace Toffoli

/-- A single control is a SUM; two controls use one Toffoli. Larger
products use the two-pass binary ladder on `d - 2` borrowed wires. -/
def binaryLadderCost (C2 d : ℕ) : ℕ :=
  if d ≤ 1 then 0 else if d = 2 then C2 else 4 * (d - 2) * C2

end Toffoli
