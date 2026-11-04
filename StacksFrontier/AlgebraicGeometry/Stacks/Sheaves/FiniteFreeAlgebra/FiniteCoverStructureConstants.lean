module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.ConjugationGroupoidComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.FiniteCoverQuotientStack

/-!
# `ℋ_d` is the quotient stack `[X/G]` of the conjugation action

Let `S` be a scheme of a big fppf site and let `d` be a positive integer. This file proves that
the category `ℋ_d` of degree-`d` finite locally free covers over the big fppf site over `S` is
equivalent to the quotient stack `[X/G]` of the conjugation action of the unit-fixing subgroup
`G ⊆ GL_d` on the scheme `X` of structure constants of free `d`-dimensional algebras.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.conjugationGroupoidIso`: the isomorphism of the presheaf
  `FA_d` of free rank-`d` algebra structures with the pointwise groupoid presheaf of the action
  groupoid of the conjugation action.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.nonempty_isEquivalenceOver_finiteCover_conjugationQuotient`:
  **`ℋ_d` is equivalent, over the big fppf site over `S`, to the quotient stack `[X/G]` of the
  conjugation action.**

## References

* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S) (d : ℕ) [NeZero d]

/-- The unit-fixing group scheme `G_S`, over the base itself, is an algebraic space over `S`. -/
theorem isAlgebraicSpace_conjugationGroup :
    IsAlgebraicSpace 𝒞 S hS
      (Space.groupOverStar 𝒞 S hS (Space.terminalSpace 𝒞 S hS).obj
        (Space.unitFixingPointsOnSite 𝒞 S hS d)).left :=
  Space.isAlgebraicSpace_groupOverStar 𝒞 S hS (Space.terminalSpace 𝒞 S hS).obj
    (Space.terminalSpace 𝒞 S hS).property (Space.unitFixingPointsOnSite 𝒞 S hS d)
    (Space.pointsOnSiteRepresentableBy 𝒞 S hS (Space.unitFixingSiteObject 𝒞 S hS d)
      (Space.unitFixingSiteObjectGrpObj 𝒞 S hS d))

/-- The scheme of structure constants `X_S`, over the base itself, is an algebraic space over
`S`. -/
theorem isAlgebraicSpace_conjugationObject :
    IsAlgebraicSpace 𝒞 S hS
      (Space.objectOverStar 𝒞 S hS (Space.terminalSpace 𝒞 S hS).obj
        (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d))).left :=
  Space.isAlgebraicSpace_objectOverStar 𝒞 S hS (Space.terminalSpace 𝒞 S hS).obj
    (Space.terminalSpace 𝒞 S hS).property
    (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d))
    (Space.yonedaRepresentableBy 𝒞 S hS (Space.structureConstantsSiteObject 𝒞 S hS d))

/-- The isomorphism of the presheaf `FA_d` of free rank-`d` algebra structures with the pointwise
groupoid presheaf of the action groupoid `conjugationGroupoidInSpaces` of the conjugation
action. -/
noncomputable abbrev conjugationGroupoidIso :
    ffaSitePresheaf 𝒞 S hS d ≅
      AlgebraicGeometry.Stack.evaluationGroupoidFunctor
        (conjugationGroupoidInSpaces 𝒞 S hS d (isAlgebraicSpace_conjugationGroup 𝒞 S hS d)
          (isAlgebraicSpace_conjugationObject 𝒞 S hS d)).toGroupoidInFunctors :=
  conjugationFfaIso 𝒞 S hS d (isAlgebraicSpace_conjugationGroup 𝒞 S hS d)
    (isAlgebraicSpace_conjugationObject 𝒞 S hS d)

/-- The category `ℋ_d` of degree-`d` finite locally free covers is equivalent, over the big fppf
site over `S`, to the quotient stack `[X/G]` of the conjugation action of the unit-fixing subgroup
`G ⊆ GL_d` on the scheme `X` of structure constants of free `d`-dimensional algebras, by the
extension of `AlgebraicGeometry.FiniteFreeAlgebra.specQuotientPrestack` across the stackification
`AlgebraicGeometry.Stack.toQuotientStack`. -/
@[stacks 05YQ "the category of degree-`d` finite locally free covers is equivalent, over the \
big fppf site over `S`, to the quotient stack `[X/G]` of the conjugation action of the \
unit-fixing subgroup `G` of `GL_d` on the scheme `X` of structure constants"]
theorem nonempty_isEquivalenceOver_finiteCover_conjugationQuotient :
    Nonempty (Functor.IsEquivalenceOver
      (Space.structureConstantsQuotientStack 𝒞 S hS d (Space.terminalSpace 𝒞 S hS)).p
      (Functor.uliftHomProj (AlgebraicGeometry.Stack.finiteCoverProjection
        (B := 𝒞) (S := S) (hS := hS) (d := d)))
      (Functor.Stackification.extend
        (AlgebraicGeometry.Stack.isFibredOneMorphism_toQuotientStack
          (conjugationGroupoidInSpaces 𝒞 S hS d (isAlgebraicSpace_conjugationGroup 𝒞 S hS d)
          (isAlgebraicSpace_conjugationObject 𝒞 S hS d)))
        (isFibredOneMorphism_specQuotientPrestack
          (conjugationGroupoidInSpaces 𝒞 S hS d (isAlgebraicSpace_conjugationGroup 𝒞 S hS d)
          (isAlgebraicSpace_conjugationObject 𝒞 S hS d))
          (conjugationGroupoidIso 𝒞 S hS d))
        (AlgebraicGeometry.Stack.isLocallyBijective_toQuotientStack
          (conjugationGroupoidInSpaces 𝒞 S hS d (isAlgebraicSpace_conjugationGroup 𝒞 S hS d)
          (isAlgebraicSpace_conjugationObject 𝒞 S hS d)))
        (isStack_uliftHomProj_finiteCoverProjection 𝒞 S hS d).isMorSheaf
        (AlgebraicGeometry.Stack.essImage_toQuotientStack
          (conjugationGroupoidInSpaces 𝒞 S hS d (isAlgebraicSpace_conjugationGroup 𝒞 S hS d)
          (isAlgebraicSpace_conjugationObject 𝒞 S hS d)))
        (isStack_uliftHomProj_finiteCoverProjection 𝒞 S hS d).hasEffectiveDescent)) :=
  nonempty_isEquivalenceOver_finiteCover_quotientStack
    (conjugationGroupoidInSpaces 𝒞 S hS d (isAlgebraicSpace_conjugationGroup 𝒞 S hS d)
      (isAlgebraicSpace_conjugationObject 𝒞 S hS d))
    (conjugationGroupoidIso 𝒞 S hS d)

end AlgebraicGeometry.FiniteFreeAlgebra

end
