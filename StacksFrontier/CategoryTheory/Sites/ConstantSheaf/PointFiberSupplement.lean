module

public import StacksFrontier.CategoryTheory.Sites.ConstantSheaf.PointFiber

/-!
# Constant sheaves on a site with a point are nonzero

On a site with a point, the constant sheaf on a nonzero object is nonzero, because its fiber at
the point is that object.

## Main results

* `CategoryTheory.GrothendieckTopology.Point.not_isZero_constantSheaf`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w vC uC vA uA

namespace CategoryTheory.GrothendieckTopology.Point

/-- **A site with a point has nonzero constant sheaves**: the fiber of the constant sheaf on a
nonzero object is that object. -/
public theorem not_isZero_constantSheaf
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    {A : Type uA} [Category.{vA} A] [HasZeroMorphisms A]
    [HasWeakSheafify J A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    (p : GrothendieckTopology.Point.{w} J) {M : A} (hM : ¬ IsZero M) :
    ¬ IsZero ((constantSheaf J A).obj M) := fun h =>
  hM ((p.sheafFiber.map_isZero h).of_iso (p.constantFiberIso J A M).symm)

end CategoryTheory.GrothendieckTopology.Point

end
