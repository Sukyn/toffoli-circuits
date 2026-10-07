import Toffoli.Universality.ModularUniversality

namespace Toffoli
open scoped Classical

/-- Prime-field universality is the prime-modulus case of modular
universality. Every prime at least five is odd. -/
theorem prime_universality {p n : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hn : 0 < n) :
    affineSwapGroup (ZMod p)
      (coordinatePermutation (⟨0, hn⟩ : Fin n) (Equiv.swap (0 : ZMod p) 1)) = ⊤ :=
  modular_universality ((Fact.out : p.Prime).odd_of_ne_two (by omega)) hp hn

end Toffoli
