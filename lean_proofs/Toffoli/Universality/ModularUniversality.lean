import Toffoli.Universality.OddRingUniversality
import Toffoli.Universality.ModularOneWire

namespace Toffoli
open scoped Classical

/-- Over every odd modulus at least five, affine maps and the fixed swap
on the first wire generate all register permutations. The one-wire base
uses translation by one, so no primality assumption is needed. -/
theorem modular_universality {q n : ℕ} (hodd : Odd q) (hq : 5 ≤ q) (hn : 0 < n) :
    affineSwapGroup (ZMod q)
      (coordinatePermutation (⟨0, hn⟩ : Fin n) (Equiv.swap (0 : ZMod q) 1)) = ⊤ := by
  letI : NeZero q := ⟨by omega⟩
  exact odd_ring_universality
    (by simpa only [ZMod.card] using hodd)
    (by simpa only [ZMod.card] using hq)
    (modular_one_wire (by omega)) hn

end Toffoli
