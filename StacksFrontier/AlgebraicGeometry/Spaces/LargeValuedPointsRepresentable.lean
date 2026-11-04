module

public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPointsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable

/-!
# Points of a represented presheaf in a larger value universe

Let `S` be a scheme contained in a big fppf site `B`. The points of the universe-lifted Yoneda
presheaf `CategoryTheory.uliftYoneda.{w}.obj U` of an object `U` of the big fppf category over
`S`, `AlgebraicGeometry.Space.pointsULift`, are the points of the representing scheme.

## Main definitions

* `AlgebraicGeometry.Space.pointsEquivSchemeULift`: the bijection between the points of the
  universe-lifted Yoneda presheaf of an object of the site and the points of the representing
  scheme.

## Main results

* `AlgebraicGeometry.Space.pointsEquivSchemeULift_class`: the bijection sends the class of a
  field-valued point to the scheme point underlying it.
* `AlgebraicGeometry.Space.pointsEquivSchemeULift_naturality`: the bijection is natural in the
  object of the site.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BV](https://stacks.math.columbia.edu/tag/03BV)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe w u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The points of the universe-lifted Yoneda presheaf of an object `U` of the big fppf category
over `S` are the points of the representing scheme. -/
noncomputable def pointsEquivSchemeULift (U : BigFppfOver B S hS) :
    pointsULift.{w} B S hS ((uliftYoneda.{w}).obj U) ≃
      (BigFppfOver.toScheme B S hS).obj U :=
  (pointsULiftEquiv.{w} B S hS (yoneda.obj U)).symm.trans (pointsEquivScheme B S hS U)

/-- The comparison bijection sends the class of a field-valued point of a universe-lifted
Yoneda presheaf to the scheme point underlying that field-valued point. -/
theorem pointsEquivSchemeULift_class (U : BigFppfOver B S hS)
    (p : FieldValuedPointULift.{w} B S hS ((uliftYoneda.{w}).obj U)) :
    pointsEquivSchemeULift.{w} B S hS U (p.class B S hS _) =
      schemePointULift.{w} B S hS U p := rfl

/-- The comparison bijection is natural in the object of the site: the map on points induced by
a morphism of the site is the underlying map of schemes. -/
theorem pointsEquivSchemeULift_naturality {V U : BigFppfOver B S hS} (q : V ⟶ U)
    (v : pointsULift.{w} B S hS ((uliftYoneda.{w}).obj V)) :
    pointsEquivSchemeULift.{w} B S hS U
        (pointsMapULift B S hS _ ((uliftYoneda.{w}).map q) v) =
      (BigFppfOver.toScheme B S hS).map q (pointsEquivSchemeULift.{w} B S hS V v) := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep v
  exact schemePointULift_map_uliftYoneda B S hS q p

end AlgebraicGeometry.Space

end
