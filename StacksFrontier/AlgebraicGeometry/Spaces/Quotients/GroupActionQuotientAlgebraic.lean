module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.GroupActionQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatRelationQuotient

/-!
# The quotient of an algebraic space by a free flat action is an algebraic space (Stacks 06PH)

Let `X ⟶ B` be a morphism of algebraic spaces and let a group algebraic space `G` over `B`,
flat and locally of finite presentation, act freely on `X` over `B`. **Stacks 06PH** says that
`X/G` is an algebraic space, that `X ⟶ X/G` is surjective, flat and locally of finite
presentation, and that `X` is an fppf `G`-torsor over `X/G`.

`StacksFrontier/AlgebraicGeometry/Spaces/Quotients/GroupActionQuotient.lean` proves the
surjectivity outright and the other assertions from the instance
`AlgebraicGeometry.Space.QuotientBootstrap` of the bootstrap theorem Stacks 04S6. This file
proves that instance from condition (1) of Stacks 04S6,
`AlgebraicGeometry.Space.bootstrap04S6QuotientSheaf`, and states the assertions without it.

## Main results

* `AlgebraicGeometry.Space.quotientBootstrap`: the instance of Stacks 04S6 consumed by
  Stacks 06PH.
* `AlgebraicGeometry.Space.isAlgebraicSpace_actionQuotientSheaf`,
  `AlgebraicGeometry.Space.isFlat_toActionQuotientSheaf`,
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_toActionQuotientSheaf` and
  `AlgebraicGeometry.Space.isFppfTorsor_actionQuotientSheaf`: **Stacks 06PH**, with
  `AlgebraicGeometry.Space.isSurjective_toActionQuotientSheaf`.

## References

* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 06PH](https://stacks.math.columbia.edu/tag/06PH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj MonoidalCategory
open scoped CategoryTheory.Obj

universe u

namespace AlgebraicGeometry.Space

variable {site : BigFppfSite.{u}} {S : Scheme.{u}} {hS : site.Contains S}
  {B : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u}

variable [HasSheafify (BigFppfOver.topology site S hS) (Type u)]

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_GroupActionQuotientAlgebraic :
    HasPullbacks ((BigFppfOver site S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- The group structure on `G` pulled back to the quotient `X/G`, carried by the monoidal
pullback functor (instance search times out without this shortcut). -/
noncomputable local instance (priority := high)
    groupOverQuotientGrpObj_GroupActionQuotientAlgebraic
    (hB : Presheaf.IsSheaf (BigFppfOver.topology site S hS) B) (G X : Over B) [GrpObj G]
    [ModObj G X] : GrpObj (groupOverQuotient hB G X) :=
  letI : (Over.pullback (actionQuotientToBase hB G X)).Monoidal :=
    Over.instBraidedPullback.toMonoidal
  Functor.grpObjObj

variable (site S hS) in
/-- The instance of the bootstrap theorem Stacks 04S6 that Stacks 06PH consumes: the quotient
sheaf of a flat, locally finitely presented equivalence relation of algebraic spaces is an
algebraic space. It is condition (1) of Stacks 04S6. -/
theorem quotientBootstrap : QuotientBootstrap site S hS :=
  fun j _ hR hU hrel hsF htF hsL htL =>
    bootstrap04S6QuotientSheaf site S hS j hR hU hrel htF htL hsF hsL

/-- **Stacks 06PH.** The quotient `X/G` of an algebraic space by a free action of a group
algebraic space which is flat and locally of finite presentation over the base is an
algebraic space. -/
@[stacks 06PH "X/G is an algebraic space"]
theorem isAlgebraicSpace_actionQuotientSheaf
    (hB : IsAlgebraicSpace site S hS B) (G X : Over B) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace site S hS G.left) (hX : IsAlgebraicSpace site S hS X.left)
    (hfree : IsFreeAction site S hS B G X) (hflat : IsFlat site S hS G.hom)
    (hfp : IsLocallyOfFinitePresentation site S hS G.hom) :
    IsAlgebraicSpace site S hS (actionQuotientSheaf G X).obj :=
  isAlgebraicSpace_actionQuotientSheaf_of_quotientBootstrap (quotientBootstrap site S hS) hB G X
    hG hX hfree hflat hfp

/-- **Stacks 06PH.** The quotient morphism `X ⟶ X/G` of a free action of a group algebraic
space which is flat and locally of finite presentation over the base is flat. -/
@[stacks 06PH "flatness of X ⟶ X/G"]
theorem isFlat_toActionQuotientSheaf
    (hB : IsAlgebraicSpace site S hS B) (G X : Over B) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace site S hS G.left) (hX : IsAlgebraicSpace site S hS X.left)
    (hfree : IsFreeAction site S hS B G X) (hflat : IsFlat site S hS G.hom)
    (hfp : IsLocallyOfFinitePresentation site S hS G.hom) :
    IsFlat site S hS (toQuotientSheaf (actionPreRelation G X)) :=
  isFlat_toActionQuotientSheaf_of_quotientBootstrap (quotientBootstrap site S hS) hB G X hG hX
    hfree hflat hfp

/-- **Stacks 06PH.** The quotient morphism `X ⟶ X/G` of a free action of a group algebraic
space which is flat and locally of finite presentation over the base is locally of finite
presentation. -/
@[stacks 06PH "local finite presentation of X ⟶ X/G"]
theorem isLocallyOfFinitePresentation_toActionQuotientSheaf
    (hB : IsAlgebraicSpace site S hS B) (G X : Over B) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace site S hS G.left) (hX : IsAlgebraicSpace site S hS X.left)
    (hfree : IsFreeAction site S hS B G X) (hflat : IsFlat site S hS G.hom)
    (hfp : IsLocallyOfFinitePresentation site S hS G.hom) :
    IsLocallyOfFinitePresentation site S hS (toQuotientSheaf (actionPreRelation G X)) :=
  isLocallyOfFinitePresentation_toActionQuotientSheaf_of_quotientBootstrap
    (quotientBootstrap site S hS) hB G X hG hX hfree hflat hfp

/-- **Stacks 06PH.** For a free action of a group algebraic space which is flat and locally of
finite presentation over the base, `X` is an fppf torsor over `X/G` under the group `G` pulled
back to `X/G`. -/
@[stacks 06PH "X is an fppf G-torsor over X/G"]
theorem isFppfTorsor_actionQuotientSheaf
    (hB : IsAlgebraicSpace site S hS B) (G X : Over B) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace site S hS G.left) (hX : IsAlgebraicSpace site S hS X.left)
    (hfree : IsFreeAction site S hS B G X) (hflat : IsFlat site S hS G.hom)
    (hfp : IsLocallyOfFinitePresentation site S hS G.hom) :
    IsFppfTorsor site S hS (actionQuotientPresheaf G X)
      (isAlgebraicSpace_actionQuotientSheaf hB G X hG hX hfree hflat hfp)
      (groupOverQuotient hB.isSheaf G X) (sourceOverQuotient G X)
      (isAlgebraicSpace_pullback site S hS G.hom (actionQuotientToBase hB.isSheaf G X) hG
        (isAlgebraicSpace_actionQuotientSheaf hB G X hG hX hfree hflat hfp) hB)
      hX :=
  isFppfTorsor_actionQuotientSheaf_of_quotientBootstrap (quotientBootstrap site S hS) hB G X hG
    hX hfree hflat hfp

end AlgebraicGeometry.Space

end
