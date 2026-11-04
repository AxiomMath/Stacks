module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfSite
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousComp
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Localization.OverPullbackMorphism
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# Morphisms of big fppf topoi of algebraic spaces

A morphism `f : Y ⟶ X` of algebraic spaces in a big fppf site of algebraic spaces induces a
morphism of the associated big fppf topoi. Its inverse image is restriction along composition
with `f`, its direct image is evaluation on the fibre product along `f`, and the inverse image
has a further left adjoint which preserves fibre products and equalizers. These morphisms of
topoi compose: for composable morphisms of algebraic spaces the direct images and the inverse
images of the composites agree with the composites canonically.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.bigFppfMorphism` is the induced morphism of big fppf
  topoi: **Stacks 0DFD**.
* `AlgebraicGeometry.BigFppfSpaceSite.bigFppfMorphism_lowerShriek` is the left adjoint of its
  inverse image.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.bigFppfMorphism_inverseImageIso` and
  `.bigFppfMorphism_pushforwardIso`: the inverse image is restriction along composition with
  `f` and the direct image is the pushforward attached to the cocontinuous composition
  functor, so the two descriptions of the morphism of topoi agree.
* `AlgebraicGeometry.BigFppfSpaceSite.bigFppfMorphism_inverseImage_sections` and
  `.bigFppfMorphism_pushforward_sections`: the sections of both images.
* `AlgebraicGeometry.BigFppfSpaceSite.bigFppfMorphism_lowerShriek_adjunction`,
  `.bigFppfMorphism_lowerShriek_preservesPullbacks` and
  `.bigFppfMorphism_lowerShriek_preservesEqualizers`: the left adjoint and its exactness.
* `AlgebraicGeometry.BigFppfSpaceSite.bigFppfMorphism_comp_pushforwardIso` and
  `.bigFppfMorphism_comp_inverseImageIso`: **Stacks 0DFE**.

## Implementation notes

The big fppf site of an algebraic space `X` of the site is the localization at `X`, so its
underlying category is the slice `Over X`, the functor of sites is `Over.pullback f` and its
left adjoint is `Over.map f`. The morphism of topoi is therefore the one attached to the
morphism of sites `Over.pullback f`, and the two comparison isomorphisms are the general
localization results `CategoryTheory.StacksRelocalization.sheafPullbackOverPullbackIso` and
`.sheafPushforwardOverMapIso`.

The section formulas are stated as canonical equivalences of sets rather than as equalities of
chosen sheaf constructions, and Stacks 0DFE is stated as a natural isomorphism of direct
images together with its adjunction mate on inverse images rather than as an equality of
morphisms of topoi, which avoids identifying chosen adjunctions and sheafifications on the
nose.

The slices of the category of algebraic spaces have equalizers and `Over.map f` preserves
connected limits by the two instances of
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfSite`, which is what the exactness of
the left adjoint needs; the fibre products of algebraic spaces themselves are Tag 043C.

## References

* [Stacks Project, Tag 0DFD](https://stacks.math.columbia.edu/tag/0DFD)
* [Stacks Project, Tag 0DFE](https://stacks.math.columbia.edu/tag/0DFE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

add_to_stacks 0DFD "postcomposition functor" CategoryTheory.Over.map
add_to_stacks 0DFD "fibre-product right adjoint" CategoryTheory.Over.pullback
add_to_stacks 0DFD "site adjunction" CategoryTheory.Over.mapPullbackAdj

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) {Y X : T.Spaces} (f : Y ⟶ X)

/-- **Stacks 0DFD.** The morphism of big fppf topoi induced by a morphism of algebraic
spaces: the functor of sites is base change along `f`, which is continuous with exact
pullback. -/
@[stacks 0DFD "the morphism of topoi"]
noncomputable def bigFppfMorphism :
    MorphismOfTopoi
      (Sheaf (BigFppfSpaceOver.topology T Y) (Type (u + 1)))
      (Sheaf (BigFppfSpaceOver.topology T X) (Type (u + 1))) :=
  (StacksRelocalization.isMorphismOfSites_overPullback T.topology f).morphismOfTopoi

/-- **Stacks 0DFD.** The inverse image is naturally restriction along composition with `f`. -/
@[stacks 0DFD "inverse-image functor"]
noncomputable def bigFppfMorphism_inverseImageIso :
    (bigFppfMorphism T f).inverseImage ≅
      (Over.map f).sheafPushforwardContinuous (Type (u + 1))
        (BigFppfSpaceOver.topology T Y) (BigFppfSpaceOver.topology T X) :=
  StacksRelocalization.sheafPullbackOverPullbackIso T.topology f

/-- **Stacks 0DFD.** The direct image agrees naturally with the pushforward attached to the
cocontinuous composition functor, so the two morphisms of topoi one can attach to `f`
coincide. -/
@[stacks 0DFD "equality of the two induced morphisms of topoi"]
noncomputable def bigFppfMorphism_pushforwardIso :
    (bigFppfMorphism T f).pushforward ≅
      (Over.map f).sheafPushforwardCocontinuous (Type (u + 1))
        (BigFppfSpaceOver.topology T Y) (BigFppfSpaceOver.topology T X) :=
  (StacksRelocalization.sheafPushforwardOverMapIso T.topology f).symm

/-- **Stacks 0DFD.** The sections of the inverse image of a sheaf over an object `V` of the
big fppf site of `Y` are its sections over `V` composed with `f`. -/
@[stacks 0DFD "inverse-image sections"]
noncomputable def bigFppfMorphism_inverseImage_sections
    (G : Sheaf (BigFppfSpaceOver.topology T X) (Type (u + 1))) (V : Over Y) :
    ((bigFppfMorphism T f).inverseImage.obj G).obj.obj (op V) ≃
      G.obj.obj (op ((Over.map f).obj V)) :=
  (((sheafToPresheaf (BigFppfSpaceOver.topology T Y) (Type (u + 1))).mapIso
    ((bigFppfMorphism_inverseImageIso T f).app G)).app (op V)).toEquiv

/-- **Stacks 0DFD.** The sections of the direct image of a sheaf over an object `U` of the big
fppf site of `X` are its sections over the fibre product of `U` with `Y` over `X`. -/
@[stacks 0DFD "direct-image sections"]
noncomputable def bigFppfMorphism_pushforward_sections
    (F : Sheaf (BigFppfSpaceOver.topology T Y) (Type (u + 1))) (U : Over X) :
    ((bigFppfMorphism T f).pushforward.obj F).obj.obj (op U) ≃
      F.obj.obj (op ((Over.pullback f).obj U)) :=
  (((sheafToPresheaf (BigFppfSpaceOver.topology T X) (Type (u + 1))).mapIso
    ((bigFppfMorphism_pushforwardIso T f).app F)).app (op U)).toEquiv.trans
      (StacksRelocalization.sheafPushforwardObjEquiv T.topology f F U)

/-- **Stacks 0DFD.** The further left adjoint of the inverse image. -/
@[stacks 0DFD "left adjoint to inverse image"]
noncomputable def bigFppfMorphism_lowerShriek :
    Sheaf (BigFppfSpaceOver.topology T Y) (Type (u + 1)) ⥤
      Sheaf (BigFppfSpaceOver.topology T X) (Type (u + 1)) :=
  (Over.map f).sheafPullback (Type (u + 1))
    (BigFppfSpaceOver.topology T Y) (BigFppfSpaceOver.topology T X)

/-- **Stacks 0DFD.** Lower shriek is left adjoint to the inverse image. -/
@[stacks 0DFD "lower-shriek adjunction"]
noncomputable def bigFppfMorphism_lowerShriek_adjunction :
    bigFppfMorphism_lowerShriek T f ⊣ (bigFppfMorphism T f).inverseImage :=
  ((Over.map f).sheafAdjunctionContinuous (Type (u + 1))
    (BigFppfSpaceOver.topology T Y)
    (BigFppfSpaceOver.topology T X)).ofNatIsoRight
      (bigFppfMorphism_inverseImageIso T f).symm

/-- **Stacks 0DFD.** Lower shriek preserves fibre products of big fppf sheaves. -/
@[stacks 0DFD "lower shriek preserves fibre products"]
theorem bigFppfMorphism_lowerShriek_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (bigFppfMorphism_lowerShriek T f) :=
  Functor.preservesLimitsOfShape_sheafPullback (Over.map f)
    (BigFppfSpaceOver.topology T Y) (BigFppfSpaceOver.topology T X) WalkingCospan

/-- **Stacks 0DFD.** Lower shriek preserves equalizers of big fppf sheaves. -/
@[stacks 0DFD "lower shriek preserves equalizers"]
theorem bigFppfMorphism_lowerShriek_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair (bigFppfMorphism_lowerShriek T f) :=
  Functor.preservesLimitsOfShape_sheafPullback (Over.map f)
    (BigFppfSpaceOver.topology T Y) (BigFppfSpaceOver.topology T X) WalkingParallelPair

section Comp

variable {X' Y' Z' : T.Spaces} (g : X' ⟶ Y') (h : Y' ⟶ Z')

/-- **Stacks 0DFE.** The direct images of composable morphisms of big fppf topoi agree
canonically with the direct image of the composite. -/
@[stacks 0DFE "direct images"]
noncomputable def bigFppfMorphism_comp_pushforwardIso :
    ((bigFppfMorphism T h).comp (bigFppfMorphism T g)).pushforward ≅
      (bigFppfMorphism T (g ≫ h)).pushforward :=
  Functor.isoWhiskerRight (bigFppfMorphism_pushforwardIso T g)
      (bigFppfMorphism T h).pushforward ≪≫
    Functor.isoWhiskerLeft ((Over.map g).sheafPushforwardCocontinuous (Type (u + 1))
      (BigFppfSpaceOver.topology T X') (BigFppfSpaceOver.topology T Y'))
      (bigFppfMorphism_pushforwardIso T h) ≪≫
    (sheafPushforwardCocontinuousCompIso (BigFppfSpaceOver.topology T X')
      (BigFppfSpaceOver.topology T Y') (BigFppfSpaceOver.topology T Z')
      (Over.map g) (Over.map h)).symm ≪≫
    (by simpa only [Over.mapComp_eq] using
      Iso.refl ((Over.map (g ≫ h)).sheafPushforwardCocontinuous (Type (u + 1))
        (BigFppfSpaceOver.topology T X') (BigFppfSpaceOver.topology T Z'))) ≪≫
    (bigFppfMorphism_pushforwardIso T (g ≫ h)).symm

/-- **Stacks 0DFE.** The inverse-image comparison is the adjunction mate of the direct-image
comparison. -/
@[stacks 0DFE "inverse images"]
noncomputable def bigFppfMorphism_comp_inverseImageIso :
    ((bigFppfMorphism T h).comp (bigFppfMorphism T g)).inverseImage ≅
      (bigFppfMorphism T (g ≫ h)).inverseImage :=
  Adjunction.leftAdjointCompIso (bigFppfMorphism T h).adj (bigFppfMorphism T g).adj
    (bigFppfMorphism T (g ≫ h)).adj (bigFppfMorphism_comp_pushforwardIso T g h)

end Comp

end AlgebraicGeometry.BigFppfSpaceSite

end
