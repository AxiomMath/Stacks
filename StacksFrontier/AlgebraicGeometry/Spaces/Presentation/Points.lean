module

public import Mathlib.Order.Setoid.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Points of a presentation of an algebraic space

Let `U/R` be an étale presentation of an algebraic space `F` over `S`. The pairs of points of
`U` which come from a point of `R` are exactly the pairs with the same image in `F`, and the
atlas is surjective on points. Together these identify the points of `F` with the quotient of
the points of `U` by that relation.

## Main definitions

* `AlgebraicGeometry.Space.Presentation.pointsRelation` is the relation on the points of the
  presenting scheme cut out by the images of the two projections from the relation scheme.

## Main results

* `AlgebraicGeometry.Space.Presentation.pointsRelation_iff` identifies that relation with
  equality of images in the algebraic space.
* `AlgebraicGeometry.Space.Presentation.pointsMap_surjective`: the atlas is surjective on
  points.

## Implementation notes

The two results are exactly what is needed to apply `Setoid.ker` and
`Setoid.quotientKerEquivOfSurjective`: the relation is the kernel of the map on points
induced by the atlas, and that map is surjective, so the quotient of `|U|` by the relation is
canonically `|F|`.

## References

* [Stacks Project, Tag 03BW](https://stacks.math.columbia.edu/tag/03BW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

add_to_stacks 03BW "equivalence relation on points" Setoid.ker
add_to_sga "3 IV 3.3.1" "category of sets" Setoid.ker
add_to_sga "4 I 10.9" "special case" Setoid.ker
add_to_stacks 03BW "canonical quotient equivalence" Setoid.quotientKerEquivOfSurjective

namespace Presentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- The relation on the points of the presenting scheme given by the image of the point set
of the relation scheme under the two projections. -/
def pointsRelation (P : Presentation B S hS F hF)
    (x y : points B S hS (yoneda.obj P.U)) : Prop :=
  ∃ r : points B S hS (yoneda.obj P.R),
    pointsMap B S hS (yoneda.obj P.R) (yoneda.map P.target) r = x ∧
      pointsMap B S hS (yoneda.obj P.R) (yoneda.map P.source) r = y

/-- **Stacks 03BW.** Two points of the presenting scheme are related by the relation scheme
exactly when they have the same image in the algebraic space. -/
@[stacks 03BW "image equivalence relation"]
theorem pointsRelation_iff (P : Presentation B S hS F hF)
    (x y : points B S hS (yoneda.obj P.U)) :
    P.pointsRelation x y ↔
      pointsMap B S hS (yoneda.obj P.U) P.toSpace x =
        pointsMap B S hS (yoneda.obj P.U) P.toSpace y := by
  constructor
  · rintro ⟨r, rfl, rfl⟩
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, P.isPullback.w]
  · intro hxy
    let R : AlgebraicSpaces B S hS := ⟨yoneda.obj P.R, isAlgebraicSpace_yoneda B S hS P.R⟩
    let U : AlgebraicSpaces B S hS := ⟨yoneda.obj P.U, isAlgebraicSpace_yoneda B S hS P.U⟩
    let X : AlgebraicSpaces B S hS := ⟨F, hF⟩
    let p : R ⟶ U := ObjectProperty.homMk (yoneda.map P.target)
    let q : R ⟶ U := ObjectProperty.homMk (yoneda.map P.source)
    let g : U ⟶ X := ObjectProperty.homMk P.toSpace
    have sq : IsPullback p q g g :=
      IsPullback.of_map_of_faithful
        (F := ObjectProperty.ι (fun G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
          IsAlgebraicSpace B S hS G)) P.isPullback
    exact exists_point_of_isPullback B S hS sq x y hxy

/-- **Stacks 03BW.** The atlas of a presentation is surjective on points. -/
@[stacks 03BW "surjectivity on points"]
theorem pointsMap_surjective (P : Presentation B S hS F hF) :
    Function.Surjective (pointsMap B S hS (yoneda.obj P.U) P.toSpace) :=
  (surjective_iff_surjective_pointsMap B S hS F hF P.U P.toSpace).mp P.surjective

end Presentation

end AlgebraicGeometry.Space

end
