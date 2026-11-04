module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Smallness

/-!
# The étale topoi of an algebraic space at the universe of the structure rings

Both étale sites of an algebraic space over a scheme of universe `u` have their objects in
`Type (u + 1)`, so the *canonical* topos of either site is the category of sheaves of sets
valued in `Type (u + 1)`.  The structure sheaf of Stacks 03G6 however takes values in
`CommRingCat.{u}`, and a ringed topos in the sense of Stacks 01D3 declares its underlying topos
to be the sheaves of sets valued in the universe of its structure *rings*.  So the topos
attached to the small étale ringed topos of an algebraic space is `Sheaf J (Type u)` — sheaves
of sets one universe *below* the objects of the site.

This file develops that topos.  It is not a formality: `Type u` is too small for Mathlib's
general sheaf machinery on a site with objects in `Type (u + 1)`, and every instance below has
to be routed through the essential smallness of the small étale site
(`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`), which is the only reason sheaves of
sets in universe `u` behave well here at all.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleChartBaseChange` is the composite of the comparison
  functor of Stacks 03G1 with the spaces-étale base change of Stacks 03G2, part (1): it sends an
  étale scheme chart `V` of `Y` to the algebraic space `X ×_Y V`, étale over `X`.

## Main results

* `AlgebraicGeometry.Space.locallySmall_spacesEtale`: the spaces-étale site of an algebraic
  space is locally small at the universe of the schemes, even though its morphisms live in
  `Type (u + 1)`.
* `AlgebraicGeometry.Space.hasLimitsOfShape_structuredArrow_comparisonFunctor_op` makes the
  comparison equivalence of Stacks 03G1 available for sheaves of sets valued in `Type u`, which
  is the universe of the structure rings.
* `AlgebraicGeometry.Space.hasSheafify_spacesEtale`: presheaves of sets valued in `Type u` on
  the spaces-étale site admit sheafification.
* `AlgebraicGeometry.Space.isRightAdjoint_sheafPushforwardContinuous_spacesBaseChange`: the
  spaces-étale direct image of Stacks 03G2, part (1) has a left adjoint on sheaves of sets
  valued in `Type u`, so `CategoryTheory.Functor.sheafPullback` and
  `CategoryTheory.Functor.sheafAdjunctionContinuous` are available there.

## Implementation notes

The chain of smallness facts is the following.  `Sch_κ` is essentially small at `u` by its size
cutoff; hence so is the big fppf site of `S`, and hence the presheaf category on it is locally
small at `u` — this is the argument already used for
`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`, and
`AlgebraicGeometry.locallySmall_presheaf_bigFppfOver` is registered here as an
instance because the *spaces*-étale site inherits local smallness from it: an algebraic space
is a presheaf and a morphism of algebraic spaces is a morphism of presheaves, so the
`Type (u + 1)`-valued hom types of the spaces-étale site are `u`-small.  Local smallness of the
target together with essential smallness of the source is exactly what
`CategoryTheory.StructuredArrow.essentiallySmall` and
`CategoryTheory.CostructuredArrow.essentiallySmall` ask for, so all the comma categories that
index the Kan extensions below are essentially small at `u` and
`CategoryTheory.Limits.hasLimitsOfShape_of_essentiallySmall` applies.

Sheafification on the spaces-étale site at `Type u` is *not* the plus construction and is not
transported from a small model — the spaces-étale site is not known to be essentially small.
It is `CategoryTheory.Functor.IsDenseSubsite.hasSheafify_of_isEquivalence`, transported along
the comparison of Stacks 03G1 from the small étale site, where sheafification at `Type u` does
come from a small model (`AlgebraicGeometry.Space.SmallEtale.instHasSheafify`).

The left adjoint of the spaces-étale direct image is obtained the same way.  The left Kan
extension along the spaces-étale base change itself does **not** exist at `Type u`: its comma
categories `CostructuredArrow` range over all of the spaces-étale site of `Y`, whose objects are
not `u`-small.  The left Kan extension along
`AlgebraicGeometry.Space.spacesEtaleChartBaseChange` does exist, because its comma categories
range over the *étale charts* of `Y`, which are `u`-small; and the direct image along the
chart base change is, by `CategoryTheory.Functor.sheafPushforwardContinuousComp`, literally the
spaces-étale direct image followed by the comparison restriction, which is an equivalence.  That
is what `AlgebraicGeometry.Space.isRightAdjoint_sheafPushforwardContinuous_spacesBaseChange`
exploits.

**What is still missing, and what it is needed for.**  With the instances of this file the
spaces-étale base change of Stacks 03G2, part (1) has, on sheaves of sets valued in `Type u`, a
direct image, an inverse image and the adjunction between them.  It is *not* known here that the
inverse image is left exact, so the pair is not yet a `MorphismOfTopoi` and
`CategoryTheory.Functor.IsMorphismOfSites` is not yet available at this universe.  The two
sufficient conditions Mathlib offers both fail: `CategoryTheory.RepresentablyFlat` is of no use
because `CategoryTheory.Functor.sheafPullbackConstruction.preservesFiniteLimits` additionally
needs the left Kan extension along the base change, which does not exist at `Type u`; and
`CategoryTheory.Functor.isMorphismOfSites_of_isTerminal` — the route taken by
`AlgebraicGeometry.Space.spacesBaseChange_isMorphismOfSites` — is stated only when the universe
of the sheaves of sets equals that of the site, which here is `u + 1`.  Left exactness would
follow from `CategoryTheory.EssentiallySmall.{u}` for the spaces-étale site, which would let the
whole site be replaced by a small model at `Type u`; that is a theorem about algebraic spaces
(every algebraic space étale over `X` is a quotient of an étale chart by an open subscheme of the
chart's self-product over `X`) and is not available.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Local smallness of the spaces-étale site -/

/-! Presheaves of sets on the big fppf site of `S` are locally small at the universe of the
schemes — the big fppf site is essentially small at `u`, so restriction along a small model is
faithful on natural transformations.  That is
`AlgebraicGeometry.locallySmall_presheaf_bigFppfOver`; the spaces-étale site inherits local
smallness from it, so it is registered as an instance here. -/

attribute [instance] AlgebraicGeometry.locallySmall_presheaf_bigFppfOver

/-- Algebraic spaces over `S` are locally small at the universe of the schemes, because they
form a full subcategory of the presheaves on the big fppf site of `S`. -/
instance locallySmall_algebraicSpaces : LocallySmall.{u} (AlgebraicSpaces B S hS) :=
  locallySmall_of_faithful
    (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))

/-- The spaces-étale site of an algebraic space is locally small at the universe of the schemes:
its morphisms are morphisms of presheaves over `X`. -/
instance locallySmall_spacesEtale (X : AlgebraicSpaces B S hS) :
    LocallySmall.{u} (SpacesEtale B S hS X) :=
  have : LocallySmall.{u} (Over X) := locallySmall_of_faithful (Over.forget X)
  locallySmall_of_faithful (SpacesEtale.inclusion B S hS X)

/-! ### The comparison of Stacks 03G1 at the universe of the structure rings -/

/-- The comma categories indexing the right Kan extension along the comparison functor of
Stacks 03G1 have limits of sets in universe `u`: they are essentially small at `u`, because the
small étale site is and the spaces-étale site is locally small.

This is what makes `AlgebraicGeometry.Space.comparisonFunctor_sheafEquivalence` — and hence the
identification of the spaces-étale topos with the small étale topos — available for sheaves of
sets valued in the universe of the structure rings. -/
instance hasLimitsOfShape_structuredArrow_comparisonFunctor_op
    (X : AlgebraicSpaces B S hS) (W : (SpacesEtale B S hS X)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow W (comparisonFunctor B S hS X).op) (Type u) :=
  have : EssentiallySmall.{u} (StructuredArrow W (comparisonFunctor B S hS X).op) :=
    inferInstance
  hasLimitsOfShape_of_essentiallySmall _ _

/-- The same comma categories have limits of abelian groups in universe `u`.

This is the coefficient category in which the sheaf underlying a module of the small étale
ringed site lives, so without this instance the right Kan extension along the comparison
functor of Stacks 03G1 is unavailable for abelian sheaves at `u` — and in particular
`(comparisonFunctor …).sheafPushforwardContinuous AddCommGrpCat.{u} …` fails to be recognised
as an equivalence by instance search, even though the `Type u`, `Type (u+1)` and
`AddCommGrpCat.{u+1}` cases all resolve. It is needed by the equalizer argument of Stacks 03H7
in its module-coefficient form, which is how Stacks 03M8 invokes it. -/
instance hasLimitsOfShape_structuredArrow_comparisonFunctor_op_addCommGrp
    (X : AlgebraicSpaces B S hS) (W : (SpacesEtale B S hS X)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow W (comparisonFunctor B S hS X).op) AddCommGrpCat.{u} :=
  have : EssentiallySmall.{u} (StructuredArrow W (comparisonFunctor B S hS X).op) :=
    inferInstance
  hasLimitsOfShape_of_essentiallySmall _ _

/-- Presheaves of sets valued in the universe of the structure rings admit sheafification on the
spaces-étale site of an algebraic space.

The spaces-étale site is not known to be essentially small, so this is not transported from a
small model; it is transported along the dense subsite inclusion of Stacks 03G1 from the small
étale site, which is essentially small. -/
instance hasSheafify_spacesEtale (X : AlgebraicSpaces B S hS) :
    HasSheafify (SpacesEtale.topology B S hS X) (Type u) :=
  Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)
    (comparisonFunctor B S hS X)

/-! ### Base change of étale charts -/

/-- Base change of the étale scheme charts of `Y` along `f : X ⟶ Y`, as a functor from the small
étale site of `Y` to the spaces-étale site of `X`: the chart `V` is sent to the algebraic space
`X ×_Y V`, which is étale over `X`.

This is the comparison functor of Stacks 03G1 for `Y` followed by the spaces-étale base change
of Stacks 03G2, part (1).  Unlike the base change itself it has `u`-small comma categories, so
left Kan extensions along it exist for sheaves of sets valued in the universe of the structure
rings. -/
noncomputable def spacesEtaleChartBaseChange {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    SmallEtale B S hS Y.1 ⥤ SpacesEtale B S hS X :=
  comparisonFunctor B S hS Y ⋙ (spacesBaseChange B S hS f).functor

/-- Base change of étale charts is continuous, being a composite of continuous functors. -/
instance isContinuous_spacesEtaleChartBaseChange {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (spacesEtaleChartBaseChange B S hS f).IsContinuous
      (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS X) :=
  Functor.isContinuous_comp _ _ _ (SpacesEtale.topology B S hS Y) _

/-- The comma categories indexing the left Kan extension along base change of étale charts have
colimits of sets in universe `u`: they are essentially small at `u`, because the small étale
site is and the spaces-étale site is locally small. -/
instance hasColimitsOfShape_costructuredArrow_spacesEtaleChartBaseChange_op
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (W : (SpacesEtale B S hS X)ᵒᵖ) :
    HasColimitsOfShape
      (CostructuredArrow (spacesEtaleChartBaseChange B S hS f).op W) (Type u) :=
  have : EssentiallySmall.{u}
      (CostructuredArrow (spacesEtaleChartBaseChange B S hS f).op W) := inferInstance
  hasColimitsOfShape_of_essentiallySmall _ _

/-- Left Kan extensions of presheaves of sets valued in the universe of the structure rings
exist along base change of étale charts. -/
instance hasPointwiseLeftKanExtension_spacesEtaleChartBaseChange
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F : (SmallEtale B S hS Y.1)ᵒᵖ ⥤ Type u) :
    (spacesEtaleChartBaseChange B S hS f).op.HasPointwiseLeftKanExtension F :=
  fun _ => inferInstance

/-! ### The spaces-étale direct image at the universe of the structure rings -/

/-- Restriction along base change of étale charts, on sheaves of sets valued in the universe of
the structure rings, is the spaces-étale direct image of Stacks 03G2, part (1) followed by the
comparison restriction of Stacks 03G1.  This holds by `rfl`, being
`CategoryTheory.Functor.sheafPushforwardContinuousComp` for the two functors whose composite
`AlgebraicGeometry.Space.spacesEtaleChartBaseChange` is. -/
theorem sheafPushforwardContinuous_spacesEtaleChartBaseChange
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)) ⋙
      (comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y) =
      (spacesEtaleChartBaseChange B S hS f).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS X) := rfl

/-- The spaces-étale direct image of Stacks 03G2, part (1) has a left adjoint on sheaves of sets
valued in the universe of the structure rings, so that
`CategoryTheory.Functor.sheafPullback` and `CategoryTheory.Functor.sheafAdjunctionContinuous`
are available at that universe.

The left Kan extension along the base change itself does not exist at this universe; the left
adjoint is obtained by composing the one along base change of étale charts, which does exist,
with the inverse of the comparison equivalence of Stacks 03G1. -/
instance isRightAdjoint_sheafPushforwardContinuous_spacesBaseChange
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).IsRightAdjoint := by
  set E := (comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type u)
    (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y) with hE
  set R := (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) with hR
  set T := (spacesEtaleChartBaseChange B S hS f).sheafPushforwardContinuous (Type u)
    (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS X) with hT
  have hcomp : R ⋙ E = T :=
    sheafPushforwardContinuous_spacesEtaleChartBaseChange B S hS f
  have hiso : T ⋙ E.asEquivalence.inverse ≅ R :=
    Functor.isoWhiskerRight (eqToIso hcomp.symm) E.asEquivalence.inverse ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft R E.asEquivalence.unitIso.symm ≪≫ Functor.rightUnitor _
  exact ((E.asEquivalence.toAdjunction.comp
    (Adjunction.ofIsRightAdjoint T)).ofNatIsoRight hiso).isRightAdjoint

end AlgebraicGeometry.Space

end
