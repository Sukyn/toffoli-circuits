import Toffoli.Mixed.MixedModel
import Toffoli.Mixed.MixedFamilySum
import Toffoli.Mixed.MixedFamilyPolarization
import Toffoli.Mixed.MixedFamilyLadder

namespace Toffoli

/-- Every recurrence tree compiles to a member of the independently defined
primitive family. Its membership, execution, exact count and locality are
certificates of the same list of gates. -/
theorem indexed_mixed_family {p d b cost : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (tree : MixedCost p hp d b cost) :
    FamilyProductConstruction p d b cost := by
  induction tree with
  | sum b => exact mixed_family_sum b
  | toffoli b =>
    -- A degree-two polarization has one singleton preparation and two powers.
    let c : Composition (2 - 1) := Composition.ones 1
    have hdegree : c.length + 1 ≤ p - 2 := by
      simp only [c, Composition.ones_length]
      omega
    have children : ∀ j, FamilyProductConstruction p (c.blocksFun j)
        (2 + b - c.blocksFun j - 1) 0 := by
      intro j n
      have hsize : c.blocksFun j = 1 := by simp [c]
      rw [hsize, show 2 + b - 1 - 1 = b by omega]
      exact mixed_family_sum (p := p) b
    have hcost : divideStepCost p c hdegree (fun _ => 0) =
        2 * optimalSquareCost p hp := by
      simp [divideStepCost, c, optimalSquareCost, optimalSquareOrder]
    rw [← hcost]
    intro n
    exact mixed_family_polarization hp (by decide : 2 ≤ 2) c hdegree (fun _ => 0) children
  | polarization hd c hdegree q _children ih =>
    exact mixed_family_polarization hp (by omega) c hdegree q ih
  | ladder hd L q _children ih =>
    exact mixed_family_ladder hd L q ih

end Toffoli
