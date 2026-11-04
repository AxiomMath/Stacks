module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidRestrictionProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackAlgebraic

/-!
# A chart of a quotient stack refined by an fppf cover is a flat presentation

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `A` over a
scheme `S` of a big fppf site, and let `f : (Sch/W)_{fppf} ⟶ [U/R]` be a 1-morphism out of the
slice of the site over an object `W`, representable by algebraic spaces. Algebraicity of `[U/R]`
hands out such an `f` whose base changes are surjective and smooth, and the converse half of
**Stacks 06PJ** needs to refine it along a surjective, flat, locally finitely presented
`b : V ⟶ W` and keep a relative property of the composite.

This file performs that refinement. The content is the universe crossing: `[U/R]` has morphisms
in `u + 1`, the slice of the site has morphisms in `u`, and
`AlgebraicGeometry.Stack.HasRelativeProperty` of **Stacks 03YK** forces the source and the target
of a 1-morphism into one morphism universe, so the composition of **Stacks 045B** cannot be
applied to `f` as it stands.

## Main definitions

* `AlgebraicGeometry.Stack.schemeStackLiftInv`: the equivalence from the universe-raised category
  of elements of the algebraic space an object of the site represents to the slice of the site
  over it — the quasi-inverse of `AlgebraicGeometry.Stack.schemeStackLift`.
* `AlgebraicGeometry.Stack.liftedChart`: a 1-morphism out of the slice of the site over `W`, read
  as a 1-morphism out of that universe-raised category of elements.

## Main results

* `AlgebraicGeometry.Stack.relativeProperty_liftedChart`: the relative property of Stacks 03YK
  passes from a chart to its universe-raised reading. The library already had the opposite
  direction, `AlgebraicGeometry.Stack.relativeProperty_schemePresentationHom`, which brings a
  verdict at the raised universe down to the clause of Stacks 026O; this brings the clause up,
  which is what a chart handed out by algebraicity needs.
* `AlgebraicGeometry.Stack.hasRelativeProperty_liftedChart_comp_cover`: **Stacks 045B for a chart
  refined by a cover.** If a chart has a relative property `P` stable under composition, and
  `b : V ⟶ W` has `P` as a morphism of the algebraic spaces the two objects represent, then the
  composite `S_V ⟶ S_W ⟶ [U/R]`, read at the raised universe, has `P` relatively.
* `AlgebraicGeometry.Stack.hasRelativeProperty_liftedChart_comp_fppfCover`: the same for a
  surjective, flat, locally finitely presented morphism of the site, at each of those three
  properties — so a chart refined by an fppf cover is a surjective, flat, locally finitely
  presented presentation of the quotient stack. Nothing is carried.

## Implementation notes

Both transports are instances of **Stacks 0457**,
`AlgebraicGeometry.Stack.relativeProperty_of_equivalences`, which this library states with the
four categories of the square in independent universes; that independence is exactly what lets
the square have a source at morphism universe `u` and a target at `u + 1`. The square used is the
one of `AlgebraicGeometry.Stack.compIdSquareIso`: the raised 1-morphism is *defined* as the
equivalence followed by the chart, so the square 2-commutes on the nose and the other horizontal
1-morphism is the identity.

The composite is not identified here with the 1-morphism presented by a point of the object
space. `AlgebraicGeometry.Stack.exists_presented_point_locallySurjective_saturation` produces a
2-isomorphism between `AlgebraicGeometry.Stack.presentedSchemeMap` and a composite of this shape;
the transport of that 2-isomorphism across the universe lift, and with it the relative property of
the presented 1-morphism, is
`AlgebraicGeometry.Stack.chartRelativeProperty_schemePresentationHom` of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.PresentedPointRestrictionProperty`.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 045A](https://stacks.math.columbia.edu/tag/045A)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 06PJ](https://stacks.math.columbia.edu/tag/06PJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u t

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {A : AlgebraicSpaces C S hS}

/-- The equivalence from the universe-raised category of elements of the algebraic space an
object `W` of the site represents to the slice of the site over `W`: lower the universe, then
apply the quasi-inverse of `AlgebraicGeometry.Stack.schemeFibredCategoryEquivalence`.

This is the quasi-inverse of `AlgebraicGeometry.Stack.schemeStackLift`. -/
noncomputable def schemeStackLiftInv (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (W : BigFppfOver C S hS) :
    (liftedSpaceStack (schemeSpace W)).val ⥤ᵇ
      (schemeFibredCategory C S hS W).val :=
  BasedFunctor.comp (liftedFibredCategoryDown (schemeSpace W))
    (schemeFibredCategoryEquivalence C S hS W).inverse

/-- `AlgebraicGeometry.Stack.schemeStackLiftInv` is an equivalence of the underlying
categories. -/
instance isEquivalence_schemeStackLiftInv (W : BigFppfOver C S hS) :
    Functor.IsEquivalence (schemeStackLiftInv C S hS W).toFunctor :=
  letI : Functor.IsEquivalence
      (liftedFibredCategoryDown (Space.representedAlgebraicSpace C S hS W)).toFunctor :=
    isEquivalence_liftedFibredCategoryDown (Space.representedAlgebraicSpace C S hS W)
  letI : Functor.IsEquivalence
      (schemeFibredCategoryEquivalence C S hS W).inverse.toFunctor :=
    (schemeFibredCategoryEquivalence C S hS W).equiv.isEquivalence_inverse
  Functor.isEquivalence_trans
    (liftedFibredCategoryDown (Space.representedAlgebraicSpace C S hS W)).toFunctor
    (schemeFibredCategoryEquivalence C S hS W).inverse.toFunctor

/-- A 1-morphism out of the slice of the site over `W`, read as a 1-morphism out of the
universe-raised category of elements of the algebraic space `W` represents. -/
noncomputable def liftedChart {G : GroupoidInAlgebraicSpaces C S hS A}
    {W : BigFppfOver C S hS}
    (f : (schemeFibredCategory C S hS W).val ⥤ᵇ quotientStack G) :
    liftedSpaceStack (schemeSpace W) ⟶
      CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G) :=
  Bicategory.InducedBicategory.mkHom
    (BasedFunctor.comp (schemeStackLiftInv C S hS W) f)

/-- `AlgebraicGeometry.Stack.liftedChart` is representable by algebraic spaces as soon as the
chart is: the universe lift of the source is an equivalence, so this is **Stacks 0457**. -/
theorem isRepresentableByAlgebraicSpaces_liftedChart
    {G : GroupoidInAlgebraicSpaces C S hS A} {W : BigFppfOver C S hS}
    (f : (schemeFibredCategory C S hS W).val ⥤ᵇ quotientStack G)
    (hf : IsRepresentableByAlgebraicSpaces C S hS f) :
    IsRepresentableByAlgebraicSpaces C S hS (liftedChart f).hom :=
  (isRepresentableByAlgebraicSpaces_iff_of_equivalences C S hS
    (𝒳' := liftedSpaceStack (schemeSpace W))
    (𝒳 := schemeFibredCategory C S hS W)
    (𝒴' := CatFiberedInGroupoids.mk (quotientStack G)
      (isFiberedInGroupoids_quotientStack G))
    (𝒴 := CatFiberedInGroupoids.mk (quotientStack G)
      (isFiberedInGroupoids_quotientStack G))
    (liftedChart f).hom f (schemeStackLiftInv C S hS W)
    (BasedFunctor.id (quotientStack G))
    (compIdSquareIso (schemeStackLiftInv C S hS W) f)).1 hf

/-- **Stacks 0457 for the relative property of a chart, read up the universe lift.** If every
algebraic space representing a base change of `f` along a scheme-valued point of `[U/R]` has `P`,
then the same holds for `AlgebraicGeometry.Stack.liftedChart` at `f`.

The hypothesis is the clause that the presentation condition of Stacks 026O carries, and so is
exactly what algebraicity of `[U/R]` hands out for its chart; the conclusion is
`AlgebraicGeometry.Stack.RelativeProperty`, which the composition of Stacks 045B consumes. -/
theorem relativeProperty_liftedChart
    (P : MorphismProperty (AlgebraicSpaces C S hS))
    {G : GroupoidInAlgebraicSpaces C S hS A} {W : BigFppfOver C S hS}
    (f : (schemeFibredCategory C S hS W).val ⥤ᵇ quotientStack G)
    (hP : ∀ (V : BigFppfOver C S hS)
      (y : BigFppfOver C V.left.1 V.left.2 ⥤ (quotientStack G).obj)
      (_hy : y ⋙ (quotientStack G).p = Over.map V.hom)
      (F : (BigFppfOver C V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace C V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom)
          (schemeFibredCategory C S hS W).val.p (quotientStack G).p y f.toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap C S hS V
        ((spacesOverSmallerBaseFunctor C V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩))) :
    RelativeProperty.{u, u + 1, u + 1} C S hS P (liftedChart f) :=
  relativeProperty_of_equivalences C S hS P
    (𝒳' := liftedSpaceStack (schemeSpace W))
    (𝒳 := schemeFibredCategory C S hS W)
    (𝒴' := CatFiberedInGroupoids.mk (quotientStack G)
      (isFiberedInGroupoids_quotientStack G))
    (𝒴 := CatFiberedInGroupoids.mk (quotientStack G)
      (isFiberedInGroupoids_quotientStack G))
    (liftedChart f).hom f (schemeStackLiftInv C S hS W)
    (BasedFunctor.id (quotientStack G))
    (compIdSquareIso (schemeStackLiftInv C S hS W) f) hP

/-- **Stacks 045B for a chart refined by a cover.** Let `P` be a property of morphisms of
algebraic spaces over `S` which is stable under base change, local on the target for the fppf
precoverage and stable under composition. If a chart `f : (Sch/W)_{fppf} ⟶ [U/R]` representable
by algebraic spaces has `P` relatively, and `b : V ⟶ W` has `P` as a morphism of the algebraic
spaces `V` and `W` represent, then the composite `S_V ⟶ S_W ⟶ [U/R]` of universe-raised
categories of elements has `P` relatively.

Nothing is carried: the first factor contributes through **Stacks 045A**
(`AlgebraicGeometry.Stack.hasRelativeProperty_liftedSpaceStackMap`) and the second through
`AlgebraicGeometry.Stack.relativeProperty_liftedChart`. -/
theorem hasRelativeProperty_liftedChart_comp_cover
    (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} C S hS)]
    [P.IsStableUnderComposition]
    {G : GroupoidInAlgebraicSpaces C S hS A} {W V : BigFppfOver C S hS}
    (f : (schemeFibredCategory C S hS W).val ⥤ᵇ quotientStack G)
    (hf : IsRepresentableByAlgebraicSpaces C S hS f)
    (hP : ∀ (T : BigFppfOver C S hS)
      (y : BigFppfOver C T.left.1 T.left.2 ⥤ (quotientStack G).obj)
      (_hy : y ⋙ (quotientStack G).p = Over.map T.hom)
      (F : (BigFppfOver C T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace C T.left.1 T.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map T.hom)
          (schemeFibredCategory C S hS W).val.p (quotientStack G).p y f.toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap C S hS T
        ((spacesOverSmallerBaseFunctor C T.left.1 S T.left.2 hS T.hom).obj ⟨F, hF⟩)))
    (b : V ⟶ W)
    (hb : P (schemeSpaceMap b :
      schemeSpace V ⟶
        schemeSpace W)) :
    HasRelativeProperty.{u, u + 1, u + 1, max u t} C S hS P
      (liftedSpaceStackMap
        (X := schemeSpace V)
        (Y := schemeSpace W) (yoneda.map b) ≫ liftedChart f)
      (isRepresentableByAlgebraicSpaces_comp_basedFunctor C S hS
        (liftedSpaceStackMap
          (X := schemeSpace V)
          (Y := schemeSpace W) (yoneda.map b)).hom
        (liftedChart f).hom
        (isRepresentableByAlgebraicSpaces_liftedSpaceStackMap
          (X := schemeSpace V)
          (Y := schemeSpace W) (yoneda.map b))
        (isRepresentableByAlgebraicSpaces_liftedChart f hf)) :=
  hasRelativeProperty_comp.{u, u + 1, u + 1, max u t} C S hS P
    (𝒳 := liftedSpaceStack (schemeSpace V))
    (𝒴 := liftedSpaceStack (schemeSpace W))
    (𝒵 := CatFiberedInGroupoids.mk (quotientStack G)
      (isFiberedInGroupoids_quotientStack G))
    (liftedSpaceStackMap
      (X := schemeSpace V)
      (Y := schemeSpace W) (yoneda.map b))
    (liftedChart f)
    (isRepresentableByAlgebraicSpaces_liftedSpaceStackMap
      (X := schemeSpace V)
      (Y := schemeSpace W) (yoneda.map b))
    (isRepresentableByAlgebraicSpaces_liftedChart f hf)
    (hasRelativeProperty_liftedSpaceStackMap.{u, max u t} P
      (X := schemeSpace V)
      (Y := schemeSpace W) (yoneda.map b) hb)
    (relativeProperty_liftedChart P f hP)

/-- The clause that a 1-morphism out of the slice of the site over `W` into `[U/R]` has a
property `P` relatively: every algebraic space representing a base change of it along a
scheme-valued point of `[U/R]` has structural morphism with `P`.

This is `AlgebraicGeometry.Stack.RelativeProperty` of **Stacks 03YK** written out, which is
necessary because the slice of the site has morphisms in `u` and `[U/R]` has morphisms in
`u + 1`, so the two are not objects of one `CategoryTheory.CatFiberedInGroupoids`. It is the
clause the presentation condition of Stacks 026O carries, hence the one algebraicity of `[U/R]`
hands out for its chart. -/
def ChartRelativeProperty (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (P : MorphismProperty (AlgebraicSpaces C S hS))
    {A : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS A}
    {W : BigFppfOver C S hS}
    (f : (schemeFibredCategory C S hS W).val ⥤ᵇ quotientStack G) : Prop :=
  ∀ (T : BigFppfOver C S hS)
    (y : BigFppfOver C T.left.1 T.left.2 ⥤ (quotientStack G).obj)
    (_hy : y ⋙ (quotientStack G).p = Over.map T.hom)
    (F : (BigFppfOver C T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace C T.left.1 T.left.2 F),
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map T.hom)
        (schemeFibredCategory C S hS W).val.p (quotientStack G).p y f.toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p) →
    P (algebraicSpaceMap C S hS T
      ((spacesOverSmallerBaseFunctor C T.left.1 S T.left.2 hS T.hom).obj ⟨F, hF⟩))

/-- **A chart of a quotient stack refined by an fppf cover is a surjective, flat, locally
finitely presented presentation.** Let `f : (Sch/W)_{fppf} ⟶ [U/R]` be a 1-morphism
representable by algebraic spaces which is relatively surjective, flat and locally of finite
presentation — for instance a chart handed out by algebraicity of `[U/R]`, which is relatively
surjective and smooth — and let `b : V ⟶ W` be a morphism of the site which is surjective, flat
and locally of finite presentation as a morphism of schemes. Then the composite
`S_V ⟶ S_W ⟶ [U/R]`, read at the morphism universe of the quotient stack, is relatively
surjective, flat and locally of finite presentation.

Nothing is carried. This is the datum that **Stacks 04WY** consumes, produced for the
composite of the chart of Stacks 026O with the fppf refinement that
`AlgebraicGeometry.Stack.exists_presented_point_locallySurjective_saturation` produces for the
converse half of **Stacks 06PJ**. -/
theorem hasRelativeProperty_liftedChart_comp_fppfCover
    {G : GroupoidInAlgebraicSpaces C S hS A} {W V : BigFppfOver C S hS}
    (f : (schemeFibredCategory C S hS W).val ⥤ᵇ quotientStack G)
    (hf : IsRepresentableByAlgebraicSpaces C S hS f)
    (hsurj : ChartRelativeProperty C S hS (Space.surjectiveMorphismProperty C S hS) f)
    (hflat : ChartRelativeProperty C S hS
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) => Space.IsFlat C S hS k.hom) f)
    (hlfp : ChartRelativeProperty C S hS
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation C S hS k.hom) f)
    (b : V ⟶ W)
    (hbsurj : Surjective ((BigFppfOver.toScheme C S hS).map b))
    (hbflat : Flat ((BigFppfOver.toScheme C S hS).map b))
    (hblfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme C S hS).map b)) :
    RelativeProperty.{u, u + 1, u + 1} C S hS (Space.surjectiveMorphismProperty C S hS)
        (liftedSpaceStackMap
          (X := schemeSpace V)
          (Y := schemeSpace W) (yoneda.map b) ≫ liftedChart f) ∧
      RelativeProperty.{u, u + 1, u + 1} C S hS
        (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) => Space.IsFlat C S hS k.hom)
        (liftedSpaceStackMap
          (X := schemeSpace V)
          (Y := schemeSpace W) (yoneda.map b) ≫ liftedChart f) ∧
      RelativeProperty.{u, u + 1, u + 1} C S hS
        (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) =>
          Space.IsLocallyOfFinitePresentation C S hS k.hom)
        (liftedSpaceStackMap
          (X := schemeSpace V)
          (Y := schemeSpace W) (yoneda.map b) ≫ liftedChart f) :=
  let : MorphismProperty.IsStableUnderComposition
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation C S hS k.hom) :=
    GroupoidInAlgebraicSpaces.isLocallyOfFinitePresentation_isStableUnderComposition C S hS
  ⟨hasRelativeProperty_liftedChart_comp_cover.{u, u}
      (Space.surjectiveMorphismProperty C S hS) f hf hsurj b
      (Space.isSurjective_yoneda_map C S hS b hbsurj),
    hasRelativeProperty_liftedChart_comp_cover.{u, u}
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) => Space.IsFlat C S hS k.hom)
      f hf hflat b (Space.isFlat_yoneda_map C S hS b hbflat),
    hasRelativeProperty_liftedChart_comp_cover.{u, u}
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation C S hS k.hom)
      f hf hlfp b (Space.isLocallyOfFinitePresentation_yoneda_map C S hS b hblfp)⟩

end AlgebraicGeometry.Stack

end
