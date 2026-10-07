import Toffoli.Foundations.IndexedTargetModel
import Toffoli.Foundations.CoordinateShearModel

namespace Toffoli

variable {K : Type*} [Field K] {n : ℕ}

/-- A control-affine gate neither changes nor reads wires outside its pool.
Preserving those wires alone would still allow their values to be read. -/
structure AffineLocal (pool : Finset (Fin n))
    (e : Controls K n ≃ᵃ[K] Controls K n) : Prop where
  outside : ∀ x i, i ∉ pool → e x i = x i
  depends : ∀ x y, (∀ i ∈ pool, x i = y i) → ∀ i ∈ pool, e x i = e y i

/-- Permitted gate forms for an accumulator call. The enclosing circuit's
locality certificate separately requires its target to lie outside the pool. -/
inductive AccumulatorGate (pool : Finset (Fin n)) :
    IndexedTarget n → MultiGate K n → Prop where
  | affine (target : IndexedTarget n) (e : Controls K n ≃ᵃ[K] Controls K n)
      (hlocal : AffineLocal pool e) : AccumulatorGate pool target (.affine e)
  | swap (target : IndexedTarget n) (i : Fin n) (hi : i ∈ pool) (a b : K) :
      AccumulatorGate pool target (.swap i a b)
  | sum (i : Fin n) (hi : i ∈ pool) (coefficient : K) :
      AccumulatorGate pool none (.sum i coefficient)
  | shear (source target : Fin n) (hsource : source ∈ pool)
      (coefficient : K) (hne : source ≠ target) :
      AccumulatorGate pool (some target)
        (.affine (coordinateShear source target coefficient hne))

/-- Every primitive gate respects the available control pool. The selected
target is excluded from that pool and is used only as a SUM destination;
all other excluded wires remain unread and unchanged at every step. -/
structure MultiCircuit.AccumulatorLocal (c : MultiCircuit K n)
    (pool : Finset (Fin n)) (target : IndexedTarget n) : Prop where
  target_outside : ∀ i ∈ pool, target ≠ some i
  gates : ∀ gate ∈ c, AccumulatorGate pool target gate

end Toffoli
