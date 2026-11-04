module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackProjection
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackValuativeExistence
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackCategory
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.CostructuredArrow
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.UliftHomStack

/-!
# The structure morphism of the Picard stack to its base

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, and let
`Picardstack_{X/B}` be the Picard stack of Section 0372, whose objects are the triples
`(U, b, L)`. Forgetting the invertible module is the structure morphism `Picardstack_{X/B} ⟶ B`
of Section 0DM9, with target the category fibred in sets `𝒮_B` of the test schemes over `B`,
`AlgebraicGeometry.Space.baseCFG`.

## Main definitions

* `AlgebraicGeometry.Space.picardToBase`: the 1-morphism `Picardstack_{X/B} ⟶ 𝒮_B`,
  `(U, b, L) ↦ (U, b)`.

## Main results

* `AlgebraicGeometry.Space.baseCFG_faithful`: the structure functor of `𝒮_Y` is faithful.

## References

* [Stacks Project, Tag 0372](https://stacks.math.columbia.edu/tag/0372)
* [Stacks Project, Section 0DM9](https://stacks.math.columbia.edu/tag/0DM9)
* [Stacks Project, Tag 08LP](https://stacks.math.columbia.edu/tag/08LP)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The structure functor of `𝒮_Y` is faithful. -/
instance baseCFG_faithful (Y : AlgebraicSpaces B S hS) : (baseCFG Y).val.p.Faithful :=
  baseBasedCategory_faithful Y

/-- **The structure morphism `Picardstack_{X/B} ⟶ 𝒮_B`** of the Picard stack: it forgets the
invertible module, sending `(U, b, L)` to the test scheme `(U, b)` over the base and a morphism
`(h, g)` to its base map `h`. -/
def picardToBase (hc : ModulePushforwardCoherence B S hS) (s : PicardSituation B S hS) :
    picardCFG hc s ⟶ baseCFG s.base :=
  letI : Category.{u + 1} (PicardObject s) := (picardCategoryData hc s).category
  Bicategory.InducedBicategory.mkHom
    { toFunctor := (picardCategoryData hc s).projection ⋙
        (ULiftHom.up : s.SchemesOver ⥤ BaseObjects s.base)
      w := rfl }

/-- The structure morphism sends a Picard object to its test scheme over the base. -/
theorem picardToBase_obj (hc : ModulePushforwardCoherence B S hS) (s : PicardSituation B S hS)
    (A : PicardObject s) :
    (picardToBase hc s).hom.obj A = ULiftHom.objUp A.T :=
  rfl

end AlgebraicGeometry.Space

end
