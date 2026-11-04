module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# The fiber of a constant sheaf at a point of a site

A point of a site `(C, J)` has a fiber functor on sheaves,
`CategoryTheory.GrothendieckTopology.Point.sheafFiber`, computed as the colimit over the
cofiltered category of elements of the point's fiber functor. This file records that the fiber
of the constant sheaf on an object `M` of the coefficient category is `M` itself.

## Main definitions

* `CategoryTheory.GrothendieckTopology.Point.constantFiberIso`: the fiber at a point of the
  constant sheaf on `M` is `M`.

## Implementation notes

The point's fiber functor on *presheaves* takes the constant presheaf on `M` to `M`, because
the category of elements of the point's fiber is cofiltered, hence connected, and a colimit of
a constant diagram over a connected category is the constant value. Passing from the constant
presheaf to the constant sheaf is harmless because the fiber functor inverts the morphisms
which sheafification inverts, so `toSheafify` becomes an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w vC uC vA uA

namespace CategoryTheory.GrothendieckTopology.Point

/-- **The fiber of a constant sheaf is its value.** For a point `p` of a site `(C, J)` and an
object `M` of the coefficient category, the fiber of the constant sheaf on `M` at `p` is
canonically isomorphic to `M`. -/
public noncomputable def constantFiberIso
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    (A : Type uA) [Category.{vA} A]
    [HasWeakSheafify J A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    (p : GrothendieckTopology.Point.{w} J) (M : A) :
    p.sheafFiber.obj ((constantSheaf J A).obj M) ≅ M := by
  let P := (Functor.const Cᵒᵖ).obj M
  haveI : IsConnected p.fiber.Elementsᵒᵖ := IsFiltered.isConnected _
  let e : p.presheafFiber.obj P ≅ M :=
    (colimit.isColimit _).coconePointUniqueUpToIso
      (Limits.isColimitConstCocone p.fiber.Elementsᵒᵖ M)
  exact (asIso (p.presheafFiber.map (CategoryTheory.toSheafify J P))).symm ≪≫ e

end CategoryTheory.GrothendieckTopology.Point

end
