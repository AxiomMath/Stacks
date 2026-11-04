module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.ModObj
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackOfAction

/-!
# Group actions on the big fppf site, read over an algebraic space

`AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSite` turns a presheaf of groups on
the big fppf site over `S` which is represented by an object of that site into a group algebraic
space `G_B = B ×_S G` over an arbitrary algebraic space `B` over `S`. This file is its
counterpart for the acted-on object: an action of such a presheaf of groups on a presheaf
represented by an object of the site becomes an action of `G_B` on `X_B = B ×_S X` in the slice
of presheaves over `B`, that is, a `CategoryTheory.ModObj`. With both halves available, the
quotient stack `[X/G]` of **Stacks 044Q** part (2) can be formed from data given purely in terms
of points.

## Main definitions

* `AlgebraicGeometry.Space.overStar`: the functor `B ⨯ -` into presheaves over `B`, with
  `AlgebraicGeometry.Space.overStarMonoidal` its monoidal structure.
* `AlgebraicGeometry.Space.groupOverStar` and `AlgebraicGeometry.Space.objectOverStar`:
  `B ×_S G` and `B ×_S X` as objects over `B`, with
  `AlgebraicGeometry.Space.groupOverStarGrpObj` the group structure and
  `AlgebraicGeometry.Space.objectOverStarModObj` the action.
* `AlgebraicGeometry.Space.quotientStackOfPointsAction`: **Stacks 044Q** part (2) for an action
  given on points.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_groupOverStar` and
  `AlgebraicGeometry.Space.isAlgebraicSpace_objectOverStar`: both are algebraic spaces as soon
  as the two presheaves are represented by objects of the site.
* `AlgebraicGeometry.Space.isStackInGroupoids_quotientStackOfPointsAction`: the resulting
  quotient stack is a stack in groupoids over the big fppf site.

## Implementation notes

`CategoryTheory.Over.star B` is right adjoint to `CategoryTheory.Over.forget B`, so it preserves
finite products and is therefore monoidal for the cartesian structures; the group object and the
action are then the images of the presheaf-level ones under it, by
`CategoryTheory.Functor.mapGrp` and `CategoryTheory.Functor.LaxMonoidal.modObj`. Nothing about
the action is chosen twice: the unit and multiplication of the image group object are literally
the transported ones, which is why `CategoryTheory.Functor.LaxMonoidal.modObj` applies with no
compatibility hypotheses to discharge.

The underlying presheaf of `(Over.star B).obj Q` is `B ⨯ Q`, so algebraicity is the same
statement as for `AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSite`, namely the
restriction of `B` to the representing object of the site, which is **Stacks 02WY** in the form
`AlgebraicGeometry.Space.isAlgebraicSpace_prod_yoneda_obj`.

## References

* [Stacks Project, Tag 043I](https://stacks.math.columbia.edu/tag/043I)
* [Stacks Project, Tag 043Q](https://stacks.math.columbia.edu/tag/043Q)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S)
  (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)

/-- The functor `Q ↦ B ⨯ Q`, read into presheaves over `B` through the first projection. -/
noncomputable abbrev overStar :
    ((BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) ⥤ Over B :=
  Over.star B

/-- `AlgebraicGeometry.Space.overStar` is monoidal: it is right adjoint to the forgetful
functor of the slice, hence preserves finite products. -/
noncomputable instance overStarMonoidal : (overStar 𝒞 S hS B).Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts _

/-- The underlying presheaf of `B ⨯ Q` over `B` is `B ⨯ Q`. -/
theorem overStar_obj_left (Q : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) :
    ((overStar 𝒞 S hS B).obj Q).left = (B ⨯ Q) :=
  rfl

/-- The group object `G_B = B ×_S G` over `B` attached to a presheaf of groups on the big fppf
site over `S`. -/
noncomputable abbrev groupOverStar (F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u}) : Over B :=
  (overStar 𝒞 S hS B).obj (F ⋙ forget GrpCat)

/-- **Stacks Project, Tag 043I.** `B ×_S G` is a group object of presheaves over `B`, with the
pointwise group law of the given presheaf of groups. -/
@[stacks 043I "the group object over `B` attached to a presheaf of groups on the site"]
noncomputable instance groupOverStarGrpObj (F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u}) :
    GrpObj (groupOverStar 𝒞 S hS B F) :=
  ((overStar 𝒞 S hS B).mapGrp.obj (.mk (F ⋙ forget GrpCat))).grp

/-- The object `X_B = B ×_S X` over `B` attached to a presheaf on the big fppf site over `S`. -/
noncomputable abbrev objectOverStar (P : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) : Over B :=
  (overStar 𝒞 S hS B).obj P

/-- **Stacks Project, Tag 043Q, part (1).** An action of a presheaf of groups on a presheaf over
the big fppf site over `S` is an action of `B ×_S G` on `B ×_S X` in presheaves over `B`. -/
@[stacks 043Q "part (1): the action over `B` attached to an action on points"]
noncomputable instance objectOverStarModObj (F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u})
    (P : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) [ModObj (F ⋙ forget GrpCat) P] :
    ModObj (groupOverStar 𝒞 S hS B F) (objectOverStar 𝒞 S hS B P) :=
  Functor.LaxMonoidal.modObj (overStar 𝒞 S hS B)
    (((overStar 𝒞 S hS B).mapGrp.obj (.mk (F ⋙ forget GrpCat))).grp).toMonObj rfl rfl

/-- `B ×_S G` is an algebraic space over `S` as soon as the presheaf of groups is represented by
an object of the site. -/
theorem isAlgebraicSpace_groupOverStar (hB : IsAlgebraicSpace 𝒞 S hS B)
    (F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u}) {a : BigFppfOver 𝒞 S hS}
    (r : (F ⋙ forget GrpCat).RepresentableBy a) :
    IsAlgebraicSpace 𝒞 S hS (groupOverStar 𝒞 S hS B F).left :=
  isAlgebraicSpace_prod_compForget_of_representableBy 𝒞 S hS B hB F r

/-- `B ×_S X` is an algebraic space over `S` as soon as the presheaf is represented by an object
of the site. -/
theorem isAlgebraicSpace_objectOverStar (hB : IsAlgebraicSpace 𝒞 S hS B)
    (P : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) {b : BigFppfOver 𝒞 S hS}
    (r : P.RepresentableBy b) :
    IsAlgebraicSpace 𝒞 S hS (objectOverStar 𝒞 S hS B P).left :=
  isAlgebraicSpace_of_iso 𝒞 S hS
    ((prod.mapIso (Iso.refl B) r.toIso.symm).trans (prod.braiding B (yoneda.obj b)))
    (isAlgebraicSpace_prod_yoneda_obj b hB)

/-- **Stacks Project, Tag 044Q, part (2)** for an action given on points: the quotient stack
`[X/G]` of a presheaf of groups acting on a presheaf, both represented by objects of the big
fppf site over `S`, read over an algebraic space `B` over `S`. -/
@[stacks 044Q "part (2) for an action given on points"]
noncomputable abbrev quotientStackOfPointsAction (B : AlgebraicSpaces 𝒞 S hS)
    (F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u}) (P : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    [ModObj (F ⋙ forget GrpCat) P] {a b : BigFppfOver 𝒞 S hS}
    (r : (F ⋙ forget GrpCat).RepresentableBy a) (s : P.RepresentableBy b) :
    BasedCategory (BigFppfOver 𝒞 S hS) :=
  Stack.quotientStackOfAction B (groupOverStar 𝒞 S hS B.obj F)
    (objectOverStar 𝒞 S hS B.obj P)
    (isAlgebraicSpace_groupOverStar 𝒞 S hS B.obj B.property F r)
    (isAlgebraicSpace_objectOverStar 𝒞 S hS B.obj B.property P s)

/-- The quotient stack of an action given on points is a stack in groupoids over the big fppf
site. -/
@[stacks 044Q "part (2) for an action given on points"]
theorem isStackInGroupoids_quotientStackOfPointsAction (B : AlgebraicSpaces 𝒞 S hS)
    (F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u}) (P : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    [ModObj (F ⋙ forget GrpCat) P] {a b : BigFppfOver 𝒞 S hS}
    (r : (F ⋙ forget GrpCat).RepresentableBy a) (s : P.RepresentableBy b) :
    Functor.IsStackInGroupoids (quotientStackOfPointsAction 𝒞 S hS B F P r s).p
      (BigFppfOver.topology 𝒞 S hS) :=
  Stack.isStackInGroupoids_quotientStackOfAction _ _ _ _ _

end AlgebraicGeometry.Space

end
