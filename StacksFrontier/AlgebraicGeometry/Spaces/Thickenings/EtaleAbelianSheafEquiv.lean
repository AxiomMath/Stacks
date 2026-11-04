module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleRingedTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos

/-!
# Abelian sheaves on the small étale sites of a thickening

`AlgebraicGeometry.Space.smallEtaleSheafEquiv_of_isThickening` is the Comparison Lemma for
sheaves of *sets* on the small étale sites of a thickening `X ⊂ X'` of algebraic spaces, at the
universe `u + 1` of the étale charts. This file supplies the same comparison for sheaves of
abelian groups with sections in the universe `u` of the schemes, which is the coefficient
category in which cohomology and the Picard group live.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_sheafPushforward_thickeningChartBaseChange`:
  restriction of abelian sheaves along chart base change is an equivalence
  `Sheaf X_étale AddCommGrpCat.{u} ≌ Sheaf X'_étale AddCommGrpCat.{u}`.

## Implementation notes

The sites here are `Type (u + 1)` categories with `Type u` morphisms, so the structured-arrow
categories which index the pointwise right Kan extension have `Type (u + 1)` objects and
`AddCommGrpCat.{u}` does not have limits of that size. They are nevertheless essentially
`u`-small, because both étale sites are: `CategoryTheory.StructuredArrow.essentiallySmall`
needs exactly essential smallness of the source and local smallness of the target, and
`CategoryTheory.hasLimitsOfShape_of_essentiallySmall` then transfers the limits. That size
input is `AlgebraicGeometry.Space.hasLimitsOfShape_structuredArrow_thickeningChartBaseChange`
of `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/EtaleRingedTopos.lean`, stated there for
an arbitrary target category with `u`-small limits; this module promotes it to a local instance
at `AddCommGrpCat.{u}`.

The cover-density input is `AlgebraicGeometry.Space.thickeningChartBaseChange_isDenseSubsite`,
which this module promotes to an instance: every consumer writing a restriction functor along
chart base change needs its continuity, and that is derived from the dense-subsite condition.

## References

* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU), the Comparison Lemma
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [instance] AlgebraicGeometry.Space.thickeningChartBaseChange_isDenseSubsite

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

attribute [local instance] hasLimitsOfShape_structuredArrow_thickeningChartBaseChange

/-- **The Comparison Lemma for abelian sheaves on the small étale sites of a thickening.**
Restriction of sheaves of abelian groups along base change of étale charts is an equivalence
from the abelian sheaves on the small étale site of a thickening `X ⊂ X'` to the abelian sheaves
on the small étale site of `X'`.

This is `AlgebraicGeometry.Space.smallEtaleSheafEquiv_of_isThickening` with coefficients in
`AddCommGrpCat.{u}` in place of `Type (u + 1)`. -/
instance isEquivalence_sheafPushforward_thickeningChartBaseChange
    (hG : IsThickening B S hS X G) :
    ((thickeningChartBaseChange B S hS hG).sheafPushforwardContinuous AddCommGrpCat.{u}
        (SmallEtale.topology B S hS X.1)
        (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1)).IsEquivalence :=
  inferInstance

end AlgebraicGeometry.Space

end
