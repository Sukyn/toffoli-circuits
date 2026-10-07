import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.List.Nodup

namespace Toffoli

/-- False denotes a positive sign, true a negative sign. Index zero changes
slowest, matching the order of group preparations in the paper. -/
abbrev GrayWord (n : ℕ) := Fin n → Bool

/-- One group update changes exactly one sign. -/
def grayFlip {n : ℕ} (word : GrayWord n) (i : Fin n) : GrayWord n :=
  Function.update word i (!word i)

/-- The reflected order: prefix + to the old order, then - to its reversal. -/
def grayWords : (n : ℕ) → List (GrayWord n)
  | 0 => [fun _ => false]
  | n + 1 => (grayWords n).map (Fin.cons false) ++
      (grayWords n).reverse.map (Fin.cons true)

/-- The executable list of sign changes. For three groups it is
[2, 1, 2, 0, 2, 1, 2], so the counts are 1, 2, and 4. -/
def grayFlips : (n : ℕ) → List (Fin n)
  | 0 => []
  | n + 1 => let shifted := (grayFlips n).map Fin.succ
      shifted ++ 0 :: shifted.reverse

end Toffoli
