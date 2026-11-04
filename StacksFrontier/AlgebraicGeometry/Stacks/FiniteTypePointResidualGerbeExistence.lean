module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointResidualGerbeFromPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalImageFieldPointCover

/-!
# Stacks 06G3, unconditionally

Let `𝒳` be an algebraic stack over `S` and let `x ∈ |𝒳|`. **Stacks 06G3** says that `x` is a
finite type point exactly when there is a one-point algebraic stack with a
locally-of-finite-type 1-morphism to `𝒳` whose image on points is `{x}`, and exactly when the
residual gerbe of `𝒳` at `x` exists with locally-of-finite-type inclusion. This file proves the
one implication `StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointResidualGerbe` carried as a
hypothesis — (1) ⟹ (3) — and restates the tag with nothing assumed.

## The route

The source's proof builds the quotient stack `[u/R]` of the self-intersection groupoid of the
field-valued point `u : Spec(k) ⟶ 𝒳` of condition (1) of **Stacks 06FX** and needs it to be an
algebraic stack, which is **Stacks 06FI**, i.e. Artin's theorem **Stacks 06DC**. This file takes
the other route: it cuts the algebraic stack out of `𝒳` as the strictly full subcategory
`AlgebraicGeometry.Stack.localImage` of the objects fppf-locally in the image of `u`, so that the
1-morphism to `𝒳` is the inclusion of a full subcategory — fully faithful for free — and the
algebraicity of the subcategory is **Stacks 05UM** at the representability of that inclusion,
which the bootstrap theorem **Stacks 04S6** part (3) supplies. The bootstrap theorem is proved in
this library, as `AlgebraicGeometry.Stack.bootstrap04S6Spaces`, so nothing is assumed.

What makes the inclusion representable is that the factorization of `u` through the subcategory is
a flat presentation of it: surjective, flat and locally of finite presentation in the relative
sense of **Stacks 03YK**. All three are relative properties of the two projections of the
self-intersection of `u`, carried to the factorization by **Stacks 045D**
(`AlgebraicGeometry.Stack.relativeProperty_toLocalImage`), and over the spectrum of a field two of
them are free; see
`StacksFrontier.AlgebraicGeometry.Stacks.LocalImageFieldPointCover`.

## Main results

* `AlgebraicGeometry.Stack.hasFullyFaithfulFiniteTypeFieldPointPresentations`: every
  locally-of-finite-type 1-morphism out of the algebraic stack of the spectrum of a field factors
  as a surjective flat 1-morphism locally of finite presentation followed by a fully faithful one.
* `AlgebraicGeometry.Stack.existsLocallyOfFiniteTypeResidualGerbe`: the implication (1) ⟹ (3) of
  **Stacks 06G3**.
* `AlgebraicGeometry.Stack.isFiniteTypePoint_tfae_unconditional`: **Stacks 06G3**, with nothing
  carried.

## Implementation notes

The three properties of the factorization are stated in this library both as the relative property
of **Stacks 03YK** and as the smooth-diagram tests of **Stacks 06PW**, **Stacks 06Q2** and
**Stacks 04ZS** that the 2-category of algebraic stacks uses. The two directions of **Stacks 06FM**
(`AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_iff_some` and
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty`) convert between
them, and **Stacks 04XI** does it for surjectivity; that conversion needs the algebraicity of both
source and target, which is why it happens only after the subcategory has been shown to be an
algebraic stack.

Composing the factorization with the inclusion returns the point on the nose
(`AlgebraicGeometry.Stack.toLocalImageBased_comp_inclusion`), so the 2-isomorphism the
factorization statement asks for is the identity.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 06G3](https://stacks.math.columbia.edu/tag/06G3)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

attribute [local instance] Space.isFlat_isStableUnderBaseChange
  Space.isLocallyOfFinitePresentation_isStableUnderBaseChange
  Space.isLocallyOfFiniteType_isStableUnderBaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The quotient presentation of a locally-of-finite-type field-valued point, proved.** Every
1-morphism `u` to an algebraic stack over `S` from the algebraic stack of the spectrum of a field
which is locally of finite type factors as a surjective flat 1-morphism locally of finite
presentation onto an algebraic stack followed by a fully faithful one.

The algebraic stack is the strictly full subcategory of the objects of the target which are
fppf-locally in the image of `u`, the fully faithful 1-morphism is its inclusion, and the
factorization is `AlgebraicGeometry.Stack.toLocalImage`. -/
theorem hasFullyFaithfulFiniteTypeFieldPointPresentations :
    HasFullyFaithfulFiniteTypeFieldPointPresentations.{u, w} B S hS := by
  intro 𝒳 F u hulft
  let hlftloc : (spaceProperty B S hS
      (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  let hflatloc : (spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  have h𝒰rep : IsRepresentableByAlgebraicSpace B S hS (schemeFibredCategory B S hS F.base) :=
    isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS F.base
  have hu : IsRepresentableByAlgebraicSpaces B S hS u.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property h𝒰rep u.hom
  have hulftRel : RelativeProperty B S hS
      (spaceProperty B S hS
        (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)) u.hom :=
    hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram.{u, u} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS) u.hom hu
      ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
        (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
        (schemeStack.{u, w} B S hS F.base).property 𝒳.property u.hom).1 hulft)
  have hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 (localImage u.hom)) :=
    isAlgebraicStack_fullSubcategoryBased_localImage_fieldPoint B S hS 𝒳 F u.hom hu hulftRel
  obtain ⟨hsurj, hflat, hlfp⟩ :=
    relativeProperty_surjective_flat_locallyOfFinitePresentation_toLocalImage
      B S hS 𝒳 F u.hom hu hulftRel
  have hz : IsRepresentableByAlgebraicSpaces B S hS (toLocalImage u.hom).hom :=
    isRepresentableByAlgebraicSpaces_toLocalImage B S hS u.hom hu
  let g : schemeStack.{u, w} B S hS F.base ⟶
      fullSubcategoryAlgebraicStack 𝒳 (localImage u.hom) hP :=
    Bicategory.InducedBicategory.mkHom (toLocalImage u.hom)
  refine ⟨fullSubcategoryAlgebraicStack 𝒳 (localImage u.hom) hP,
    fullSubcategoryInclusion 𝒳 (localImage u.hom) hP, g,
    ObjectProperty.full_ι (localImage u.hom), ObjectProperty.faithful_ι (localImage u.hom),
    ?_, ?_, ?_, ⟨Iso.refl _⟩⟩
  · exact (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      (schemeStack.{u, w} B S hS F.base).property hP (toLocalImage u.hom)).2
      (hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS _ hP
        (toLocalImage u.hom) hz hlfp)
  · exact (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS g hz).2 hsurj
  · exact (AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS g).2
      (hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS _ hP
        (toLocalImage u.hom) hz hflat)

/-- **The implication (1) ⟹ (3) of Stacks 06G3.** At a finite type point of an algebraic stack
over `S` the residual gerbe exists and its inclusion is locally of finite type.

This is `AlgebraicGeometry.Stack.existsLocallyOfFiniteTypeResidualGerbe_of_hasPresentation` at the
presentation `AlgebraicGeometry.Stack.hasFullyFaithfulFiniteTypeFieldPointPresentations`, which is
proved rather than assumed. -/
theorem existsLocallyOfFiniteTypeResidualGerbe (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    ExistsLocallyOfFiniteTypeResidualGerbeOfIsFiniteTypePoint.{u, w} B S hS 𝒳 :=
  existsLocallyOfFiniteTypeResidualGerbe_of_hasPresentation.{u, w} B S hS
    (hasFullyFaithfulFiniteTypeFieldPointPresentations.{u, w} B S hS) 𝒳

/-- **Stacks 06G3.** For a point `x` of the point space of an algebraic stack `𝒳` over `S`, the
following are equivalent: `x` is a finite type point; there is a one-point algebraic stack with a
locally-of-finite-type 1-morphism to `𝒳` whose image on points is `{x}`; the residual gerbe of
`𝒳` at `x` exists and its inclusion is locally of finite type.

All three implications are proved. (1) ⟹ (3) is
`AlgebraicGeometry.Stack.existsLocallyOfFiniteTypeResidualGerbe`, which builds the one-point
algebraic stack as the strictly full subcategory of the objects of `𝒳` fppf-locally in the image
of the field-valued point of condition (1) of **Stacks 06FX**; (3) ⟹ (2) is
`AlgebraicGeometry.Stack.hasSingletonLocallyOfFiniteTypeCoverAt_of_residualGerbe` and (2) ⟹ (1) is
`AlgebraicGeometry.Stack.isFiniteTypePoint_of_hasSingletonLocallyOfFiniteTypeCoverAt`. -/
@[stacks 06G3 "the equivalence of (1) being a finite type point, (2) admitting a \
locally-of-finite-type 1-morphism from a one-point algebraic stack with image the point, and \
(3) the residual gerbe existing with locally-of-finite-type inclusion. All three implications \
are proved and nothing is assumed: (1) => (3) cuts the one-point algebraic stack out of the \
target as the strictly full subcategory of the objects fppf-locally in the image of the \
field-valued point, whose inclusion is fully faithful and, by Stacks 05UM at the bootstrap \
theorem Stacks 04S6 part (3), representable by algebraic spaces"]
theorem isFiniteTypePoint_tfae_unconditional (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val 𝒳.val.property) :
    [IsFiniteTypePoint.{u, w} B S hS 𝒳 x,
      HasSingletonLocallyOfFiniteTypeCoverAt.{u, w} B S hS 𝒳 x,
      HasLocallyOfFiniteTypeResidualGerbeAt.{u, w} B S hS 𝒳 x].TFAE := by
  tfae_have 1 → 3 := existsLocallyOfFiniteTypeResidualGerbe.{u, w} B S hS 𝒳 x
  tfae_have 3 → 2 := hasSingletonLocallyOfFiniteTypeCoverAt_of_residualGerbe.{u, w} B S hS 𝒳 x
  tfae_have 2 → 1 := isFiniteTypePoint_of_hasSingletonLocallyOfFiniteTypeCoverAt.{u, w} B S hS 𝒳 x
  tfae_finish

end AlgebraicGeometry.Stack

end
