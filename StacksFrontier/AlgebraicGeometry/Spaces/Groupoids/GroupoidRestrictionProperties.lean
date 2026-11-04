module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidRestriction

/-!
# Permanence of the source and target maps under restriction of a groupoid in algebraic spaces

Let `G` be a groupoid in algebraic spaces over an algebraic space `Bs` over a scheme `S` of a
big fppf site, and let `g : U' ⟶ G.objects` be a morphism of algebraic spaces. The restriction
of `G` along `g` has `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionSource` and
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionTarget` for its two structure maps.
This file shows that each of them inherits any property of morphisms of algebraic spaces over
`S` which is stable under base change and under composition, from that property holding of `g`
and of the corresponding structure map of `G`.

Instantiated at being locally of finite type, being locally of finite presentation and
flatness, this is Stacks **04RP**, parts (1), (2) and (3).

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.prop_restrictionSource` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.prop_restrictionTarget`: the statement for an
  arbitrary property of morphisms of algebraic spaces over `S` stable under base change and
  composition.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isLocallyOfFiniteType_restrictionSource` and
  `…_restrictionTarget`: Stacks 04RP part (1).
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isLocallyOfFinitePresentation_restrictionSource`
  and `…_restrictionTarget`: Stacks 04RP part (2).
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isFlat_restrictionSource` and
  `…_restrictionTarget`: Stacks 04RP part (3).

## Implementation notes

The whole content is a factorisation of each structure map of the restriction into two base
changes. Writing `A = U' ×_{g, G.objects, t} G.arrows` and `A' = G.arrows ×_{s, G.objects, g} U'`
for the two fibre products out of which
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrows` is built as `A ×_{G.arrows} A'`:

* `restrictionSource` is, definitionally, the projection `A ×_{G.arrows} A' ⟶ A'` followed by
  the projection `A' ⟶ U'`. The second is the base change of `s` along `g`; the first is the
  base change of `A ⟶ G.arrows`, which is itself the base change of `g` along `t`. So the
  source map of the restriction needs the property only of `s` and of `g`.
* `restrictionTarget` is the projection `A ×_{G.arrows} A' ⟶ A` followed by `A ⟶ U'`. The
  second is the base change of `t` along `g`; the first is the base change of
  `A' ⟶ G.arrows`, which is the base change of `g` along `s`. So the target map needs the
  property only of `t` and of `g`.

That split is sharper than the source's, which asks for the property of both `s` and `t` for
either conclusion, and it is the reason the two generic lemmas are stated separately rather
than as one conjunction.

The two stability assumptions are taken as explicit hypotheses rather than as instances,
because the three instantiations in the library supply them as terms: base change from
`AlgebraicGeometry.Space.isLocallyOfFiniteType_isStableUnderBaseChange` (**Stacks 03XH**),
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isStableUnderBaseChange`
(**Stacks 03XR**) and `AlgebraicGeometry.Space.isFlat_isStableUnderBaseChange`
(**Stacks 03MO**), and composition from `AlgebraicGeometry.Space.isLocallyOfFiniteType_comp`
(**Stacks 03XG**), `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_comp`
(**Stacks 03XQ**) and `AlgebraicGeometry.Space.isFlat_isStableUnderComposition`
(**Stacks 03MN**). The first two composition facts are stated for morphisms of presheaves with
the algebraicity of the three objects as hypotheses, so the category-level instance is assembled
here from the objects' own `property` fields, exactly as
`StacksFrontier/AlgebraicGeometry/Spaces/FlatComposition.lean` does for flatness. Those two
assemblies — `isLocallyOfFiniteType_isStableUnderComposition` and
`isLocallyOfFinitePresentation_isStableUnderComposition` — are auxiliary to this file and are
kept inside this namespace rather than beside
`AlgebraicGeometry.Space.isFlat_isStableUnderComposition`, where their natural home is, so that
a Chapter 67 landing of the missing category-level instances collides with nothing; whoever
lands those should promote these two and repoint the four corollaries below at them.

Stacks 04RP's part (4) is "Add more here" in the source and has no content.

## Tag withheld: 04RP is a Chapter 79 tag

Stacks 04RP is `spaces-more-groupoids`, **Chapter 79**. No `stacks` attribute for 04RP is
placed here, and none is placed for 03XG, 03XH, 03XQ, 03XR, 03MN, 03MO or 044B, all of which
are already registered elsewhere in this library. The declarations are left unregistered here.

## References

* [Stacks Project, Tag 04RP](https://stacks.math.columbia.edu/tag/04RP)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {Bs : AlgebraicSpaces C S hS}

/-- The second projection of a fibre product of algebraic spaces has any base-change-stable
property of morphisms which the first factor map has. -/
private theorem prop_fiberProductSnd
    (P : MorphismProperty (AlgebraicSpaces C S hS)) (hbc : P.IsStableUnderBaseChange)
    {X Y Z : AlgebraicSpaces C S hS} (f : X ⟶ Z) (g : Y ⟶ Z) (hf : P f) :
    P (fiberProductSnd f g) :=
  hbc.of_isPullback (AlgebraicSpaces.isPullback_fiberProduct C S hS f g) hf

/-- The first projection of a fibre product of algebraic spaces has any base-change-stable
property of morphisms which the second factor map has. -/
private theorem prop_fiberProductFst
    (P : MorphismProperty (AlgebraicSpaces C S hS)) (hbc : P.IsStableUnderBaseChange)
    {X Y Z : AlgebraicSpaces C S hS} (f : X ⟶ Z) (g : Y ⟶ Z) (hg : P g) :
    P (fiberProductFst f g) :=
  hbc.of_isPullback (AlgebraicSpaces.isPullback_fiberProduct C S hS f g).flip hg

/-- The source map of the restriction of a groupoid in algebraic spaces along `g` has any
property of morphisms of algebraic spaces over `S` which is stable under base change and under
composition, as soon as the source map of the groupoid and `g` have it.

The map factors as the base change along `A' ⟶ G.arrows` of the base change of `g` along the
target map, followed by the base change of the source map along `g`. -/
public theorem prop_restrictionSource
    (P : MorphismProperty (AlgebraicSpaces C S hS))
    (hbc : P.IsStableUnderBaseChange) (hcomp : P.IsStableUnderComposition)
    (G : GroupoidInAlgebraicSpaces C S hS Bs)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (hs : P G.source) (hg : P g) :
    P (restrictionSource G g) :=
  hcomp.comp_mem _ _
    (prop_fiberProductSnd P hbc _ _ (prop_fiberProductSnd P hbc _ _ hg))
    (prop_fiberProductSnd P hbc _ _ hs)

/-- The target map of the restriction of a groupoid in algebraic spaces along `g` has any
property of morphisms of algebraic spaces over `S` which is stable under base change and under
composition, as soon as the target map of the groupoid and `g` have it.

The map factors as the base change along `A ⟶ G.arrows` of the base change of `g` along the
source map, followed by the base change of the target map along `g`. -/
public theorem prop_restrictionTarget
    (P : MorphismProperty (AlgebraicSpaces C S hS))
    (hbc : P.IsStableUnderBaseChange) (hcomp : P.IsStableUnderComposition)
    (G : GroupoidInAlgebraicSpaces C S hS Bs)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (ht : P G.target) (hg : P g) :
    P (restrictionTarget G g) :=
  hcomp.comp_mem _ _
    (prop_fiberProductFst P hbc _ _ (prop_fiberProductFst P hbc _ _ hg))
    (prop_fiberProductFst P hbc _ _ ht)

/-- Being locally of finite type is stable under composition as a property of morphisms of the
category of algebraic spaces over `S`. This is `Stacks 03XG` with the algebraicity of the three
objects supplied by the objects themselves. -/
public theorem isLocallyOfFiniteType_isStableUnderComposition
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S) :
    MorphismProperty.IsStableUnderComposition
      (fun ⦃F G : AlgebraicSpaces C S hS⦄ (f : F ⟶ G) =>
        Space.IsLocallyOfFiniteType C S hS f.hom) :=
  ⟨fun {X Y Z} f h hf hh => Space.isLocallyOfFiniteType_comp C S hS X.property Y.property
    Z.property f.hom h.hom hf hh⟩

/-- Being locally of finite presentation is stable under composition as a property of morphisms
of the category of algebraic spaces over `S`. This is `Stacks 03XQ` with the algebraicity of the
three objects supplied by the objects themselves. -/
public theorem isLocallyOfFinitePresentation_isStableUnderComposition
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S) :
    MorphismProperty.IsStableUnderComposition
      (fun ⦃F G : AlgebraicSpaces C S hS⦄ (f : F ⟶ G) =>
        Space.IsLocallyOfFinitePresentation C S hS f.hom) :=
  ⟨fun {X Y Z} f h hf hh => Space.isLocallyOfFinitePresentation_comp C S hS X.property
    Y.property Z.property f.hom h.hom hf hh⟩

/-- **Stacks 04RP, part (1).** If the source map of a groupoid in algebraic spaces and `g` are
locally of finite type, then so is the source map of the restriction along `g`. -/
public theorem isLocallyOfFiniteType_restrictionSource
    (G : GroupoidInAlgebraicSpaces C S hS Bs)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (hs : Space.IsLocallyOfFiniteType C S hS G.source.hom)
    (hg : Space.IsLocallyOfFiniteType C S hS g.hom) :
    Space.IsLocallyOfFiniteType C S hS (restrictionSource G g).hom :=
  prop_restrictionSource _ (Space.isLocallyOfFiniteType_isStableUnderBaseChange C S hS)
    (isLocallyOfFiniteType_isStableUnderComposition C S hS) G g hs hg

/-- **Stacks 04RP, part (1).** If the target map of a groupoid in algebraic spaces and `g` are
locally of finite type, then so is the target map of the restriction along `g`. -/
public theorem isLocallyOfFiniteType_restrictionTarget
    (G : GroupoidInAlgebraicSpaces C S hS Bs)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (ht : Space.IsLocallyOfFiniteType C S hS G.target.hom)
    (hg : Space.IsLocallyOfFiniteType C S hS g.hom) :
    Space.IsLocallyOfFiniteType C S hS (restrictionTarget G g).hom :=
  prop_restrictionTarget _ (Space.isLocallyOfFiniteType_isStableUnderBaseChange C S hS)
    (isLocallyOfFiniteType_isStableUnderComposition C S hS) G g ht hg

/-- **Stacks 04RP, part (2).** If the source map of a groupoid in algebraic spaces and `g` are
locally of finite presentation, then so is the source map of the restriction along `g`. -/
public theorem isLocallyOfFinitePresentation_restrictionSource
    (G : GroupoidInAlgebraicSpaces C S hS Bs)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (hs : Space.IsLocallyOfFinitePresentation C S hS G.source.hom)
    (hg : Space.IsLocallyOfFinitePresentation C S hS g.hom) :
    Space.IsLocallyOfFinitePresentation C S hS (restrictionSource G g).hom :=
  prop_restrictionSource _
    (Space.isLocallyOfFinitePresentation_isStableUnderBaseChange C S hS)
    (isLocallyOfFinitePresentation_isStableUnderComposition C S hS) G g hs hg

/-- **Stacks 04RP, part (2).** If the target map of a groupoid in algebraic spaces and `g` are
locally of finite presentation, then so is the target map of the restriction along `g`. -/
public theorem isLocallyOfFinitePresentation_restrictionTarget
    (G : GroupoidInAlgebraicSpaces C S hS Bs)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (ht : Space.IsLocallyOfFinitePresentation C S hS G.target.hom)
    (hg : Space.IsLocallyOfFinitePresentation C S hS g.hom) :
    Space.IsLocallyOfFinitePresentation C S hS (restrictionTarget G g).hom :=
  prop_restrictionTarget _
    (Space.isLocallyOfFinitePresentation_isStableUnderBaseChange C S hS)
    (isLocallyOfFinitePresentation_isStableUnderComposition C S hS) G g ht hg

/-- **Stacks 04RP, part (3).** If the source map of a groupoid in algebraic spaces and `g` are
flat, then so is the source map of the restriction along `g`. -/
public theorem isFlat_restrictionSource
    (G : GroupoidInAlgebraicSpaces C S hS Bs)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (hs : Space.IsFlat C S hS G.source.hom) (hg : Space.IsFlat C S hS g.hom) :
    Space.IsFlat C S hS (restrictionSource G g).hom :=
  prop_restrictionSource _ (Space.isFlat_isStableUnderBaseChange C S hS)
    (Space.isFlat_isStableUnderComposition C S hS) G g hs hg

/-- **Stacks 04RP, part (3).** If the target map of a groupoid in algebraic spaces and `g` are
flat, then so is the target map of the restriction along `g`. -/
public theorem isFlat_restrictionTarget
    (G : GroupoidInAlgebraicSpaces C S hS Bs)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (ht : Space.IsFlat C S hS G.target.hom) (hg : Space.IsFlat C S hS g.hom) :
    Space.IsFlat C S hS (restrictionTarget G g).hom :=
  prop_restrictionTarget _ (Space.isFlat_isStableUnderBaseChange C S hS)
    (Space.isFlat_isStableUnderComposition C S hS) G g ht hg

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
