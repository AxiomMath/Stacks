module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientAtlasFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientAtlasPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SmoothGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionRelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact

/-!
# The quotient stack of a smooth groupoid in algebraic spaces is algebraic

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `A` over a
scheme `S` of a big fppf site, and suppose `s` and `t` are smooth (**Stacks 04TH**). **Stacks
04TK** says that the quotient stack `[U/R]` of Stacks 044Q is then an algebraic stack over `S`.

The source's proof checks the three conditions of **Stacks 026O**. Fibredness in groupoids and
the two stack clauses are Stacks 044Q, and the diagonal clause is **Stacks 04WZ**; for a quotient
stack all three are already discharged by
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_hasSmoothPresentation`, so the whole
content is the presentation clause: a *scheme* `W` over `S` and a surjective smooth 1-morphism
`(Sch/W)_{fppf} ⟶ [U/R]`. That is built here, exactly as in the source: choose a scheme `W` with
a surjective étale `W ⟶ U`, which gives a surjective smooth 1-morphism `S_W ⟶ S_U` by **Stacks
045A** and **Stacks 045F**, and compose it with the canonical projection `S_U ⟶ [U/R]` of
Stacks 044R using **Stacks 04X0** and **Stacks 045B**.

## Main definitions

* `AlgebraicGeometry.Stack.liftedSpaceStack`: the category of elements of an algebraic space with
  its morphism universe raised to the one the quotient stack lives at.
* `AlgebraicGeometry.Stack.liftedSpaceStackMap`: the 1-morphism between two of those attached to a
  morphism of algebraic spaces by **Stacks 0458**.
* `AlgebraicGeometry.Stack.schemePresentationHom`: the presentation 1-morphism
  `(Sch/W)_{fppf} ⟶ [U/R]` built from a scheme atlas `W ⟶ U` of the object space.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_liftedSpaceStackMap`: **Stacks 045A** read at the
  universe-raised categories of elements.
* `AlgebraicGeometry.Stack.relativeProperty_schemePresentationHom`: the presentation 1-morphism
  has, relatively, every property of morphisms of algebraic spaces that the scheme atlas and the
  source map of the groupoid both have.
* `AlgebraicGeometry.Stack.hasSmoothPresentation_quotientStack_of_isSmooth`: the presentation
  clause of Stacks 026O for the quotient stack of a smooth groupoid.
* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_isSmooth`: **Stacks 04TK**.

## Implementation notes

**The universe crossing is the only technical content.** The canonical projection
`AlgebraicGeometry.Stack.quotientStackProjectionHom` goes out of
`AlgebraicGeometry.Stack.liftedObjectSpace`, the category of elements of the object space with its
morphisms raised to `u + 1`, because the hom sets of a stackification are not small; so it is a
1-morphism of `CategoryTheory.CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1}`, whereas
`AlgebraicGeometry.Stack.schemeFibredCategory` and the categories of elements of algebraic spaces
live at `{u, u, u + 1, u + 1}`. Stacks 045B
(`AlgebraicGeometry.Stack.hasRelativeProperty_comp`) composes 1-morphisms of *one* 2-category, so
the scheme atlas has to be raised before it can be composed with the projection, and the composite
has to be brought back down afterwards: the presentation clause of
`AlgebraicGeometry.Stack.IsAlgebraicStack` asks for a based functor out of the *unraised* slice.

Both crossings are instantiations of Stacks 0457, which this library already states with the two
sides of the square in independent universes: `relativeProperty_of_equivalences` has four
independent pairs for the raw quantifier, and
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences` likewise for
representability. The raising functor `CategoryTheory.ULiftHom.up` and its inverse
`CategoryTheory.ULiftHom.down` commute with the projection to the site on the nose, which is why
`AlgebraicGeometry.Stack.liftedSpaceStackMapSquareIso` and the two identity squares used at the
end are `CategoryTheory.Iso.refl`.

**The isomorphism sheaves.** **Stacks 04TB**,
`AlgebraicGeometry.Stack.isAlgebraicSpace_isomPresheaf`, gives
`AlgebraicGeometry.Stack.QuotientStackIsomSheavesAlgebraic` for this quotient stack, which is
what `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_hasSmoothPresentation` asks for
(the diagonal clause, Stacks 04WZ) and which also gives the representability of the projection
`π : 𝒮_U ⟶ [U/R]`, through
`AlgebraicGeometry.Stack.representable_quotientStackProjectionHom_of_isomPresheafAlgebraic`.

**Stacks 04X0 enters through a `AlgebraicGeometry.Stack.QuotientAtlas.Presentation`**, which
bundles **Stacks 04M9** — the identification of the canonical self-square of the projection with
the arrow space — together with the representability of the projection. The lemmas below take it
as an argument; for Stacks 04TK it is built by `AlgebraicGeometry.Stack.QuotientAtlas.presentation`
from Stacks 04M9 and the representability supplied by Stacks 04TB. With it,
`AlgebraicGeometry.Stack.QuotientAtlas.hasRelativeProperty` turns smoothness of `s` into relative
smoothness of the projection, which is Stacks 04X0, and surjectivity of the projection needs no
hypothesis on the groupoid at all.

Only smoothness of the *source* map is used, as in Stacks 04X0; the smoothness of the target map
that Stacks 04TH also demands is not needed for this statement, so `hG` is consumed through
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.IsSmooth.source` alone.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 045A](https://stacks.math.columbia.edu/tag/045A)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045F](https://stacks.math.columbia.edu/tag/045F)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04TB](https://stacks.math.columbia.edu/tag/04TB)
* [Stacks Project, Tag 04TH](https://stacks.math.columbia.edu/tag/04TH)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 04WZ](https://stacks.math.columbia.edu/tag/04WZ)
* [Stacks Project, Tag 04X0](https://stacks.math.columbia.edu/tag/04X0)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w t

section Lifted

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- The category of elements of an algebraic space over `S`, with its morphism universe raised to
the one the quotient stack lives at, as a category fibred in groupoids over the big fppf site.

For the object space of a groupoid in algebraic spaces this is
`AlgebraicGeometry.Stack.liftedObjectSpace` on the nose. -/
abbrev liftedSpaceStack (X : AlgebraicSpaces C S hS) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver C S hS) :=
  CatFiberedInGroupoids.mk (liftedFibredCategory X)
    (isFiberedInGroupoids_uliftHom _ (fibredCategory C S hS X.obj).property)

/-- The universe lift of the object space of a groupoid in algebraic spaces is the universe lift
of its object space read as an algebraic space. -/
theorem liftedObjectSpace_eq {A : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS A) :
    liftedObjectSpace G = liftedSpaceStack G.objects :=
  rfl

/-- The canonical 1-morphism up into the universe lift is an equivalence of the underlying
categories: it is `CategoryTheory.ULiftHom.up`. -/
instance isEquivalence_liftedFibredCategoryUp (X : AlgebraicSpaces C S hS) :
    Functor.IsEquivalence (liftedFibredCategoryUp X).toFunctor :=
  (ULiftHom.equiv : (fibredCategory C S hS X.obj).val.obj ≌
    ULiftHom.{u + 1} (fibredCategory C S hS X.obj).val.obj).isEquivalence_functor

section Identity

universe v₁ t₁ v₂ t₂ v₃ t₃

/-- The identity based functor on a based category over the big fppf site of `S` is an
equivalence of the underlying categories. -/
instance isEquivalence_idBasedFunctor
    (𝒵 : BasedCategory.{v₃, t₃} (BigFppfOver C S hS)) :
    Functor.IsEquivalence (BasedFunctor.id 𝒵).toFunctor :=
  inferInstanceAs (Functor.IsEquivalence (𝟭 𝒵.obj))

/-- **The identity 2-commutative square on a composite 1-morphism of based categories.** It is
the datum Stacks 0457 asks for when the only equivalence in the square is the one on the source:
the composite itself is taken as the other vertical 1-morphism, and the identity closes the
square.

Stated for abstract based categories so that the definitional check is performed once here
rather than at each instance, where the two sides are large terms. -/
def compIdSquareIso
    {𝒳 : BasedCategory.{v₁, t₁} (BigFppfOver C S hS)}
    {𝒴 : BasedCategory.{v₂, t₂} (BigFppfOver C S hS)}
    {𝒵 : BasedCategory.{v₃, t₃} (BigFppfOver C S hS)}
    (a : 𝒳 ⥤ᵇ 𝒴) (f : 𝒴 ⥤ᵇ 𝒵) :
    BasedFunctor.comp a f ≅
      BasedFunctor.comp (BasedFunctor.comp a f) (BasedFunctor.id 𝒵) :=
  Iso.refl _

end Identity

/-- **Stacks 0458 at the universe-raised categories of elements.** The 1-morphism of universe
lifts attached to a morphism of algebraic spaces over `S`: lower the universe, apply
`AlgebraicGeometry.Stack.associatedMap`, raise it again. -/
def liftedSpaceStackMap {X Y : AlgebraicSpaces C S hS} (a : X.obj ⟶ Y.obj) :
    liftedSpaceStack X ⟶ liftedSpaceStack Y :=
  Bicategory.InducedBicategory.mkHom
    (BasedFunctor.comp (liftedFibredCategoryDown X)
      (BasedFunctor.comp (associatedMap C S hS a).1.hom (liftedFibredCategoryUp Y)))

/-- The square exhibiting `AlgebraicGeometry.Stack.liftedSpaceStackMap` as a transport of
`AlgebraicGeometry.Stack.associatedMap` along the two universe lifts. It 2-commutes on the nose,
because lowering the universe after raising it is the identity functor. -/
def liftedSpaceStackMapSquareIso {X Y : AlgebraicSpaces C S hS} (a : X.obj ⟶ Y.obj) :
    BasedFunctor.comp (liftedFibredCategoryDown X) (associatedMap C S hS a).1.hom ≅
      BasedFunctor.comp (liftedSpaceStackMap a).hom (liftedFibredCategoryDown Y) :=
  Iso.refl _

/-- A 1-morphism between the categories of elements of two algebraic spaces over `S` is
representable by algebraic spaces: this is **Stacks 02ZZ** against **Stacks 04SV**. -/
theorem isRepresentableByAlgebraicSpaces_associatedMap {X Y : AlgebraicSpaces C S hS}
    (a : X.obj ⟶ Y.obj) :
    IsRepresentableByAlgebraicSpaces C S hS (associatedMap C S hS a).1.hom :=
  isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace C S hS
    (associatedMap C S hS a).1
    (isRepresentableByAlgebraicSpace_fibredCategory C S hS X.obj X.property)
    (isRepresentableByAlgebraicSpace_fibredCategory C S hS Y.obj Y.property)

/-- The universe-raised 1-morphism of **Stacks 0458** is representable by algebraic spaces, by
Stacks 0457 against `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_associatedMap`. -/
theorem isRepresentableByAlgebraicSpaces_liftedSpaceStackMap {X Y : AlgebraicSpaces C S hS}
    (a : X.obj ⟶ Y.obj) :
    IsRepresentableByAlgebraicSpaces C S hS (liftedSpaceStackMap a).hom :=
  (isRepresentableByAlgebraicSpaces_iff_of_equivalences C S hS
    (𝒳' := liftedSpaceStack X) (𝒳 := fibredCategory C S hS X.obj)
    (𝒴' := liftedSpaceStack Y) (𝒴 := fibredCategory C S hS Y.obj)
    (liftedSpaceStackMap a).hom (associatedMap C S hS a).1.hom
    (liftedFibredCategoryDown X) (liftedFibredCategoryDown Y)
    (liftedSpaceStackMapSquareIso a)).1 (isRepresentableByAlgebraicSpaces_associatedMap a)

/-- **Stacks 045A at the universe-raised categories of elements.** If a morphism of algebraic
spaces over `S` has the property `P`, then the 1-morphism of universe-raised categories of
elements it induces has `P` relatively in the sense of Stacks 03YK.

The Stacks 04XB bridge is crossed on the unraised side, where both categories are represented by
presheaves of `Type u` with the identity comparison, and the verdict is carried across the
universe lift by Stacks 0457. -/
theorem hasRelativeProperty_liftedSpaceStackMap
    (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, t} C S hS)]
    {X Y : AlgebraicSpaces C S hS} (a : X.obj ⟶ Y.obj)
    (hP : P (ObjectProperty.homMk a : X ⟶ Y)) :
    HasRelativeProperty.{u, u + 1, u + 1, t} C S hS P (liftedSpaceStackMap a)
      (isRepresentableByAlgebraicSpaces_liftedSpaceStackMap a) := by
  refine hasRelativeProperty_of_equivalences_representingMap.{u, t} C S hS P
    (𝒳' := liftedSpaceStack X) (𝒴' := liftedSpaceStack Y)
    (𝒜 := fibredCategory C S hS X.obj) (𝒞 := fibredCategory C S hS Y.obj)
    (liftedSpaceStackMap a) (isRepresentableByAlgebraicSpaces_liftedSpaceStackMap a)
    (associatedMap C S hS a).1 (isRepresentableByAlgebraicSpaces_associatedMap a)
    (liftedFibredCategoryDown X) (liftedFibredCategoryDown Y)
    (liftedSpaceStackMapSquareIso a) X.obj Y.obj X.property Y.property
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) ?_
  rw [representingMap_associatedMap]
  exact hP

end Lifted

section Presentation

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {A : AlgebraicSpaces C S hS}

/-- The equivalence from the slice of the big fppf site over a scheme `W` to the universe lift of
the category of elements of the algebraic space `W` represents. It is
`AlgebraicGeometry.Stack.schemeFibredCategoryEquivalence` followed by the universe lift, so both
factors are equivalences of the underlying categories. -/
noncomputable def schemeStackLift (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (W : BigFppfOver C S hS) :
    (schemeFibredCategory C S hS W).val ⥤ᵇ
      (liftedSpaceStack (Space.representedAlgebraicSpace C S hS W)).val :=
  BasedFunctor.comp (schemeFibredCategoryEquivalence C S hS W).functor
    (liftedFibredCategoryUp (Space.representedAlgebraicSpace C S hS W))

/-- `AlgebraicGeometry.Stack.schemeStackLift` is an equivalence of the underlying categories. -/
instance isEquivalence_schemeStackLift (W : BigFppfOver C S hS) :
    Functor.IsEquivalence (schemeStackLift C S hS W).toFunctor :=
  let : Functor.IsEquivalence (schemeFibredCategoryEquivalence C S hS W).functor.toFunctor :=
    (schemeFibredCategoryEquivalence C S hS W).equiv.isEquivalence_functor
  let : Functor.IsEquivalence
      (liftedFibredCategoryUp (Space.representedAlgebraicSpace C S hS W)).toFunctor :=
    isEquivalence_liftedFibredCategoryUp (Space.representedAlgebraicSpace C S hS W)
  Functor.isEquivalence_trans (schemeFibredCategoryEquivalence C S hS W).functor.toFunctor
    (liftedFibredCategoryUp (Space.representedAlgebraicSpace C S hS W)).toFunctor

/-- The universe-raised scheme atlas of the object space of a groupoid in algebraic spaces, as a
1-morphism into `AlgebraicGeometry.Stack.liftedObjectSpace`.

This is `AlgebraicGeometry.Stack.liftedSpaceStackMap` with its target written in the spelling the
canonical projection `AlgebraicGeometry.Stack.quotientStackProjectionHom` uses for its source;
the two agree on the nose, since the object space of the groupoid read as an algebraic space is
what both universe lifts are taken of. -/
noncomputable def liftedSchemeAtlas {G : GroupoidInAlgebraicSpaces C S hS A}
    {W : BigFppfOver C S hS} (α : yoneda.obj W ⟶ G.objects.obj) :
    liftedSpaceStack (Space.representedAlgebraicSpace C S hS W) ⟶ liftedObjectSpace G :=
  liftedSpaceStackMap (X := Space.representedAlgebraicSpace C S hS W) (Y := G.objects) α

/-- `AlgebraicGeometry.Stack.liftedSchemeAtlas` is representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_liftedSchemeAtlas
    {G : GroupoidInAlgebraicSpaces C S hS A} {W : BigFppfOver C S hS}
    (α : yoneda.obj W ⟶ G.objects.obj) :
    IsRepresentableByAlgebraicSpaces C S hS (liftedSchemeAtlas α).hom :=
  isRepresentableByAlgebraicSpaces_liftedSpaceStackMap
    (X := Space.representedAlgebraicSpace C S hS W) (Y := G.objects) α

/-- **Stacks 045A for the universe-raised scheme atlas.** If the scheme atlas `α : W ⟶ U` of the
object space has `P`, then `AlgebraicGeometry.Stack.liftedSchemeAtlas` has `P` relatively. -/
theorem hasRelativeProperty_liftedSchemeAtlas
    (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, t} C S hS)]
    {G : GroupoidInAlgebraicSpaces C S hS A} {W : BigFppfOver C S hS}
    (α : yoneda.obj W ⟶ G.objects.obj)
    (hα : P (ObjectProperty.homMk α : Space.representedAlgebraicSpace C S hS W ⟶ G.objects)) :
    HasRelativeProperty.{u, u + 1, u + 1, t} C S hS P (liftedSchemeAtlas α)
      (isRepresentableByAlgebraicSpaces_liftedSchemeAtlas α) :=
  hasRelativeProperty_liftedSpaceStackMap.{u, t} P
    (X := Space.representedAlgebraicSpace C S hS W) (Y := G.objects) α hα

/-- **Stacks 04X0 from a presentation of the projection.** If the source map of the groupoid has
`P`, then the canonical projection `S_U ⟶ [U/R]` of Stacks 044R has `P` relatively.

This is `AlgebraicGeometry.Stack.QuotientAtlas.hasRelativeProperty` with the precoverage universe
of the locality instance written in the form the composition of Stacks 045B consumes. -/
theorem hasRelativeProperty_quotientStackProjectionHom_of_presentation
    (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} C S hS)]
    {G : GroupoidInAlgebraicSpaces C S hS A} (Pres : QuotientAtlas.Presentation G)
    (hsource : P G.source) :
    HasRelativeProperty.{u, u + 1, u + 1, max u t} C S hS P (quotientStackProjectionHom G)
      Pres.representable :=
  QuotientAtlas.hasRelativeProperty.{u, t} Pres P hsource

/-- The 1-morphism from the universe lift of a scheme atlas of the object space to the quotient
stack: the raised atlas of **Stacks 0458** followed by the canonical projection `S_U ⟶ [U/R]` of
**Stacks 044R**. -/
noncomputable def liftedSchemeAtlasProjection {G : GroupoidInAlgebraicSpaces C S hS A}
    {W : BigFppfOver C S hS} (α : yoneda.obj W ⟶ G.objects.obj) :
    liftedSpaceStack (Space.representedAlgebraicSpace C S hS W) ⟶
      CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G) :=
  liftedSchemeAtlas α ≫ quotientStackProjectionHom G

/-- `AlgebraicGeometry.Stack.liftedSchemeAtlasProjection` is representable by algebraic spaces, by
**Stacks 0301** from the raised atlas and the projection. -/
theorem isRepresentableByAlgebraicSpaces_liftedSchemeAtlasProjection
    {G : GroupoidInAlgebraicSpaces C S hS A} {W : BigFppfOver C S hS}
    (α : yoneda.obj W ⟶ G.objects.obj)
    (hπ : IsRepresentableByAlgebraicSpaces C S hS (quotientStackProjectionHom G).hom) :
    IsRepresentableByAlgebraicSpaces C S hS
      (liftedSchemeAtlas α ≫ quotientStackProjectionHom G).hom :=
  isRepresentableByAlgebraicSpaces_comp_basedFunctor C S hS
    (liftedSchemeAtlas α).hom (quotientStackProjectionHom G).hom
    (isRepresentableByAlgebraicSpaces_liftedSchemeAtlas α) hπ

/-- **Stacks 045B for the raised atlas followed by the projection.** If a scheme atlas
`α : W ⟶ U` of the object space has `P`, and the source map of the groupoid has `P`, then the
composite `S_W ⟶ S_U ⟶ [U/R]` has `P` relatively.

The first factor contributes through **Stacks 045A**
(`AlgebraicGeometry.Stack.hasRelativeProperty_liftedSchemeAtlas`) and the second through
**Stacks 04X0** (`AlgebraicGeometry.Stack.QuotientAtlas.hasRelativeProperty` on the
presentation `Pres`). -/
theorem hasRelativeProperty_liftedSchemeAtlasProjection
    (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} C S hS)]
    [P.IsStableUnderComposition]
    {G : GroupoidInAlgebraicSpaces C S hS A} (Pres : QuotientAtlas.Presentation G)
    {W : BigFppfOver C S hS} (α : yoneda.obj W ⟶ G.objects.obj)
    (hα : P (ObjectProperty.homMk α : Space.representedAlgebraicSpace C S hS W ⟶ G.objects))
    (hsource : P G.source) :
    HasRelativeProperty.{u, u + 1, u + 1, max u t} C S hS P
      (liftedSchemeAtlas α ≫ quotientStackProjectionHom G)
      (isRepresentableByAlgebraicSpaces_liftedSchemeAtlasProjection α Pres.representable) :=
  hasRelativeProperty_comp.{u, u + 1, u + 1, max u t} C S hS P
    (𝒳 := liftedSpaceStack (Space.representedAlgebraicSpace C S hS W))
    (𝒴 := liftedObjectSpace G)
    (𝒵 := CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G))
    (liftedSchemeAtlas α) (quotientStackProjectionHom G)
    (isRepresentableByAlgebraicSpaces_liftedSchemeAtlas α) Pres.representable
    (hasRelativeProperty_liftedSchemeAtlas.{u, max u t} P α hα)
    (hasRelativeProperty_quotientStackProjectionHom_of_presentation.{u, t} P Pres hsource)

/-- **The presentation 1-morphism of Stacks 026O for a quotient stack.** From a scheme atlas
`α : W ⟶ U` of the object space of a groupoid in algebraic spaces, the composite
`(Sch/W)_{fppf} ⟶ S_U ⟶ [U/R]`. -/
noncomputable def schemePresentationHom {G : GroupoidInAlgebraicSpaces C S hS A}
    {W : BigFppfOver C S hS} (α : yoneda.obj W ⟶ G.objects.obj) :
    (schemeFibredCategory C S hS W).val ⥤ᵇ quotientStack G :=
  BasedFunctor.comp (schemeStackLift C S hS W)
    (liftedSchemeAtlas α ≫ quotientStackProjectionHom G).hom

/-- `AlgebraicGeometry.Stack.schemePresentationHom` is representable by algebraic spaces: the
universe lift of the source is an equivalence, so this is Stacks 0457 against
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_liftedSchemeAtlasProjection`. -/
theorem isRepresentableByAlgebraicSpaces_schemePresentationHom
    {G : GroupoidInAlgebraicSpaces C S hS A} {W : BigFppfOver C S hS}
    (α : yoneda.obj W ⟶ G.objects.obj)
    (hπ : IsRepresentableByAlgebraicSpaces C S hS (quotientStackProjectionHom G).hom) :
    IsRepresentableByAlgebraicSpaces C S hS (schemePresentationHom α) :=
  (isRepresentableByAlgebraicSpaces_iff_of_equivalences C S hS
    (𝒳' := schemeFibredCategory C S hS W)
    (𝒳 := liftedSpaceStack (Space.representedAlgebraicSpace C S hS W))
    (𝒴' := CatFiberedInGroupoids.mk (quotientStack G)
      (isFiberedInGroupoids_quotientStack G))
    (𝒴 := CatFiberedInGroupoids.mk (quotientStack G)
      (isFiberedInGroupoids_quotientStack G))
    (schemePresentationHom α) (liftedSchemeAtlas α ≫ quotientStackProjectionHom G).hom
    (schemeStackLift C S hS W) (BasedFunctor.id (quotientStack G))
    (compIdSquareIso (schemeStackLift C S hS W)
      (liftedSchemeAtlas α ≫ quotientStackProjectionHom G).hom)).1
    (isRepresentableByAlgebraicSpaces_liftedSchemeAtlasProjection α hπ)

/-- **The relative property of the presentation 1-morphism.** Let `P` be a property of morphisms
of algebraic spaces over `S` which is stable under base change, local on the target for the fppf
precoverage, and stable under composition. If a scheme atlas `α : W ⟶ U` of the object space has
`P`, and the source map of the groupoid has `P`, then the presentation 1-morphism
`(Sch/W)_{fppf} ⟶ [U/R]` has `P` relatively in the sense of Stacks 03YK, written out as the
quantifier of `AlgebraicGeometry.Stack.HasRelativeProperty` so that the clause of Stacks 026O can
consume it directly.

The composite at the raised universe is
`AlgebraicGeometry.Stack.hasRelativeProperty_liftedSchemeAtlasProjection`, and Stacks 0457 brings
it down along the equivalence `AlgebraicGeometry.Stack.schemeStackLift`. -/
theorem relativeProperty_schemePresentationHom
    (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} C S hS)]
    [P.IsStableUnderComposition]
    {G : GroupoidInAlgebraicSpaces C S hS A} (Pres : QuotientAtlas.Presentation G)
    {W : BigFppfOver C S hS} (α : yoneda.obj W ⟶ G.objects.obj)
    (hα : P (ObjectProperty.homMk α : Space.representedAlgebraicSpace C S hS W ⟶ G.objects))
    (hsource : P G.source) :
    ∀ (V : BigFppfOver C S hS)
      (y : BigFppfOver C V.left.1 V.left.2 ⥤ (quotientStack G).obj)
      (_hy : y ⋙ (quotientStack G).p = Over.map V.hom)
      (F : (BigFppfOver C V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace C V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom)
          (schemeFibredCategory C S hS W).val.p (quotientStack G).p y
          (schemePresentationHom α).toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap C S hS V
        ((spacesOverSmallerBaseFunctor C V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)) :=
  relativeProperty_of_equivalences C S hS P
    (𝒳' := schemeFibredCategory C S hS W)
    (𝒳 := liftedSpaceStack (Space.representedAlgebraicSpace C S hS W))
    (𝒴' := CatFiberedInGroupoids.mk (quotientStack G)
      (isFiberedInGroupoids_quotientStack G))
    (𝒴 := CatFiberedInGroupoids.mk (quotientStack G)
      (isFiberedInGroupoids_quotientStack G))
    (schemePresentationHom α)
    (liftedSchemeAtlas α ≫ quotientStackProjectionHom G).hom (schemeStackLift C S hS W)
    (BasedFunctor.id (quotientStack G))
    (compIdSquareIso (schemeStackLift C S hS W)
      (liftedSchemeAtlas α ≫ quotientStackProjectionHom G).hom)
    (hasRelativeProperty_liftedSchemeAtlasProjection.{u, t} P Pres α hα hsource)

/-- **The presentation clause of Stacks 026O for the quotient stack of a smooth groupoid.** A
scheme over `S` with a 1-morphism to `[U/R]`, representable by algebraic spaces, relatively
surjective and relatively smooth.

Stacks 04M9 enters through the presentation `Pres`; see the implementation notes. Only
smoothness of the source map of the groupoid is used. -/
theorem hasSmoothPresentation_quotientStack_of_isSmooth
    {G : GroupoidInAlgebraicSpaces C S hS A} (Pres : QuotientAtlas.Presentation G)
    (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G) :
    QuotientStackHasSmoothPresentation C S hS G := by
  obtain ⟨W, α, hαsurj, hαsmooth⟩ :=
    Space.exists_isSurjective_isSmooth_atlas C S hS G.objects.property
  refine ⟨W, schemePresentationHom α,
    isRepresentableByAlgebraicSpaces_schemePresentationHom α Pres.representable,
    fun V y hy F hF hE => ⟨?_, ?_⟩⟩
  · exact relativeProperty_schemePresentationHom.{u, u}
      (Space.surjectiveMorphismProperty C S hS) Pres α hαsurj
      (QuotientAtlas.isSurjective_source G) V y hy F hF hE
  · exact relativeProperty_schemePresentationHom.{u, u}
      (Space.smoothMorphismProperty C S hS) Pres α hαsmooth hG.source V y hy F hF hE

/-- Let `S` be a scheme contained in a big fppf site, and let `G = (U, R, s, t, c)` be a smooth
groupoid in algebraic spaces over an algebraic space `A` over `S`. Then the quotient stack `[U/R]`
is an algebraic stack over `S`. -/
@[stacks 04TK]
theorem isAlgebraicStack_quotientStack_of_isSmooth
    {G : GroupoidInAlgebraicSpaces C S hS A}
    (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G) :
    IsAlgebraicStack.{u, w} C S hS (quotientStack G) :=
  have hisom : QuotientStackIsomSheavesAlgebraic C S hS G := fun T x y =>
    isAlgebraicSpace_isomPresheaf C S hS A G T x y
  isAlgebraicStack_quotientStack_of_hasSmoothPresentation G hisom
    (hasSmoothPresentation_quotientStack_of_isSmooth
      (QuotientAtlas.presentation G
        (representable_quotientStackProjectionHom_of_isomPresheafAlgebraic G hisom)) hG)

end Presentation

end AlgebraicGeometry.Stack

end
