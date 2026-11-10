module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionOfConstructible

/-!
# Constant sheaves with torsion value are torsion

`Stacks.Torsion.torsionSheafProperty_constantSheaf` shows that a constant abelian sheaf with
finite value is torsion. The argument only uses that every element of the value has finite
order, so it applies to any torsion abelian group.

## Main results

* `Stacks.Torsion.torsionSheafProperty_constantSheaf_of_isAddTorsion` — a constant abelian sheaf
  with torsion value is torsion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.Torsion

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **A constant abelian sheaf with torsion value is torsion.** Every element of the value is
annihilated by its order, so the constant presheaf is pointwise torsion, and the canonical map to
its sheafification is locally surjective. A finite value is torsion, `isAddTorsion_of_finite`, so
this generalizes `Stacks.Torsion.torsionSheafProperty_constantSheaf`. -/
public theorem torsionSheafProperty_constantSheaf_of_isAddTorsion
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (E : AddCommGrpCat.{w}) (hE : IsAddTorsion E) :
    torsionSheafProperty J ((constantSheaf J AddCommGrpCat.{w}).obj E) := by
  refine torsionSheafProperty_sheafify J ((Functor.const Cᵒᵖ).obj E) fun U y => ?_
  refine ⟨⊤, J.top_mem U, fun V g _ => ⟨addOrderOf (y : E), (hE (y : E)).addOrderOf_pos, ?_⟩⟩
  change addOrderOf (y : E) • y = 0
  exact addOrderOf_nsmul_eq_zero _

end Stacks.Torsion
