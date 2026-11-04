module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhSite
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Localization.OverPullbackMorphism
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizationTriangle
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# Morphisms of big ph topoi of algebraic spaces

A morphism `f : Y ⟶ X` of algebraic spaces in a big ph site of algebraic spaces induces a
morphism of the associated big ph topoi. Its inverse image is restriction along composition
with `f`, its direct image is computed by base change along `f`, and the inverse image itself
has a left adjoint which preserves fibre products and equalizers. These morphisms of topoi
compose: for composable morphisms of algebraic spaces the direct images and the inverse
images of the composites agree with the composites canonically.

## Main definitions

* `AlgebraicGeometry.BigPHSpaceSite.bigPHMorphism` is the induced morphism of big ph topoi:
  **Stacks 0DFN**.
* `AlgebraicGeometry.BigPHSpaceSite.bigPHMorphismLowerShriek` is the left adjoint of its
  inverse image.

## Main results

* `AlgebraicGeometry.BigPHSpaceSite.bigPHMorphismInverseImageIso` and
  `.bigPHMorphismPushforwardIso`: the inverse image is restriction along composition with `f`
  and the direct image is restriction along base change by `f`.
* `AlgebraicGeometry.BigPHSpaceSite.bigPHMorphismLowerShriekAdjunction`,
  `.bigPHMorphismLowerShriek_preservesPullbacks` and
  `.bigPHMorphismLowerShriek_preservesEqualizers`: the left adjoint and its exactness.
* `AlgebraicGeometry.BigPHSpaceSite.bigPHMorphism_comp_pushforwardIso` and
  `.bigPHMorphism_comp_inverseImageIso`: **Stacks 0DFP**.

## Implementation notes

The big ph site of an algebraic space `X` of the site is the localization at `X`, so its
underlying category is the slice `Over X` and the functors of the source are `Over.map f` and
`Over.pullback f`. Their adjunction, the cocontinuity of the first and the continuity of the
second are the general localization results, registered here for this site rather than
restated.

With that, the morphism of topoi is assembled from the cocontinuous pushforward as direct
image and the continuous pushforward as inverse image, so the inverse-image formula of the
source holds definitionally and the direct-image description is the adjoint comparison
`CategoryTheory.Adjunction.sheafPushforwardCocontinuousIso`. The source states Stacks 0DFP as
an equality of morphisms of topoi; it is recorded here as a natural isomorphism of direct
images together with its adjunction mate on inverse images, which avoids identifying chosen
adjunctions and sheafifications on the nose.

The slices of the category of algebraic spaces have equalizers and `Over.map f` preserves
connected limits by the two instances of
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfSite`, which is what the exactness of
the left adjoint needs.

## References

* [Stacks Project, Tag 0DFN](https://stacks.math.columbia.edu/tag/0DFN)
* [Stacks Project, Tag 0DFP](https://stacks.math.columbia.edu/tag/0DFP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigPHSpaceSite

add_to_stacks 0DFN "postcomposition functor" CategoryTheory.Over.map
add_to_stacks 0DFN "fibre-product right adjoint" CategoryTheory.Over.pullback
add_to_stacks 0DFN "site adjunction" CategoryTheory.Over.mapPullbackAdj
add_to_stacks 0DFN "cocontinuity of postcomposition" map_isCocontinuous
add_to_stacks 0DFN "continuity of postcomposition" map_isContinuous
add_to_stacks 0DFN "continuous base change"
  StacksRelocalization.isMorphismOfSites_overPullback
add_to_stacks 0DFN "agreement of the induced morphisms"
  StacksRelocalization.sheafPushforwardOverMapIso
add_to_stacks 0DFN "inverse-image sections"
  CategoryTheory.Functor.sheafPushforwardContinuous_obj_obj_obj
add_to_stacks 0DFN "direct-image sections"
  StacksRelocalization.sheafPushforwardObjEquiv

variable {S : Scheme.{u}} (T : BigPHSpaceSite S) {Y X : T.Spaces} (f : Y ⟶ X)

/-- **Stacks 0DFN.** The morphism of big ph topoi induced by a morphism of algebraic spaces:
its direct image is the cocontinuous pushforward along composition with `f` and its inverse
image is the continuous pushforward along the same functor, so sections of the inverse image
are given by `CategoryTheory.Functor.sheafPushforwardContinuous_obj_obj_obj`. -/
@[stacks 0DFN "the morphism of topoi", sga "4 IV 4.7" "special case"]
noncomputable def bigPHMorphism :
    MorphismOfTopoi
      (Sheaf (BigPHSpaceOver.topology T Y) (Type (u + 1)))
      (Sheaf (BigPHSpaceOver.topology T X) (Type (u + 1))) where
  pushforward := (Over.map f).sheafPushforwardCocontinuous (Type (u + 1))
    (BigPHSpaceOver.topology T Y) (BigPHSpaceOver.topology T X)
  inverseImage := (Over.map f).sheafPushforwardContinuous (Type (u + 1))
    (BigPHSpaceOver.topology T Y) (BigPHSpaceOver.topology T X)
  adj := (Over.map f).sheafAdjunctionCocontinuous (Type (u + 1))
    (BigPHSpaceOver.topology T Y) (BigPHSpaceOver.topology T X)
  preservesFiniteLimits := inferInstance

/-- **Stacks 0DFN.** The inverse image is restriction along composition with `f`. -/
@[stacks 0DFN "inverse-image formula"]
noncomputable def bigPHMorphismInverseImageIso :
    (bigPHMorphism T f).inverseImage ≅
      (Over.map f).sheafPushforwardContinuous (Type (u + 1))
        (BigPHSpaceOver.topology T Y) (BigPHSpaceOver.topology T X) :=
  Iso.refl _

/-- **Stacks 0DFN.** The direct image is restriction along base change by `f`, which is the
adjoint comparison of the cocontinuous pushforward with the continuous pushforward along the
right adjoint of `Over.map f`. -/
@[stacks 0DFN "direct-image formula and agreement of the induced morphisms"]
noncomputable def bigPHMorphismPushforwardIso :
    (bigPHMorphism T f).pushforward ≅
      (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (BigPHSpaceOver.topology T X) (BigPHSpaceOver.topology T Y) :=
  (Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso (Type (u + 1))

/-- **Stacks 0DFN.** The left adjoint of the inverse image of
`AlgebraicGeometry.BigPHSpaceSite.bigPHMorphism`. -/
@[stacks 0DFN "lower shriek"]
noncomputable def bigPHMorphismLowerShriek :
    Sheaf (BigPHSpaceOver.topology T Y) (Type (u + 1)) ⥤
      Sheaf (BigPHSpaceOver.topology T X) (Type (u + 1)) :=
  (Over.map f).sheafPullback (Type (u + 1))
    (BigPHSpaceOver.topology T Y) (BigPHSpaceOver.topology T X)

/-- **Stacks 0DFN.** Lower shriek is left adjoint to the inverse image. -/
@[stacks 0DFN "lower-shriek adjunction"]
noncomputable def bigPHMorphismLowerShriekAdjunction :
    bigPHMorphismLowerShriek T f ⊣ (bigPHMorphism T f).inverseImage :=
  (Over.map f).sheafAdjunctionContinuous (Type (u + 1))
    (BigPHSpaceOver.topology T Y) (BigPHSpaceOver.topology T X)

/-- **Stacks 0DFN.** Lower shriek preserves fibre products. -/
@[stacks 0DFN "lower shriek preserves fibre products"]
noncomputable instance bigPHMorphismLowerShriek_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (bigPHMorphismLowerShriek T f) :=
  Functor.preservesLimitsOfShape_sheafPullback (Over.map f)
    (BigPHSpaceOver.topology T Y) (BigPHSpaceOver.topology T X) WalkingCospan

/-- **Stacks 0DFN.** Lower shriek preserves equalizers. -/
@[stacks 0DFN "lower shriek preserves equalizers"]
noncomputable instance bigPHMorphismLowerShriek_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair (bigPHMorphismLowerShriek T f) :=
  Functor.preservesLimitsOfShape_sheafPullback (Over.map f)
    (BigPHSpaceOver.topology T Y) (BigPHSpaceOver.topology T X) WalkingParallelPair

section Comp

variable {Z : T.Spaces} (g : X ⟶ Z)

/-- **Stacks 0DFP.** The direct image of the composite agrees canonically with the composite
of the direct images on the big ph topoi, because base change along a composite is the
composite of the base changes. -/
@[stacks 0DFP "direct-image composition"]
noncomputable def bigPHMorphism_comp_pushforwardIso :
    ((bigPHMorphism T g).comp (bigPHMorphism T f)).pushforward ≅
      (bigPHMorphism T (f ≫ g)).pushforward :=
  Functor.isoWhiskerRight (bigPHMorphismPushforwardIso T f) _ ≪≫
    Functor.isoWhiskerLeft _ (bigPHMorphismPushforwardIso T g) ≪≫
    Functor.sheafPushforwardContinuousComp' (F := Over.pullback g)
      (G := Over.pullback f) (FG := Over.pullback (f ≫ g))
      (Over.pullbackComp f g).symm (Type (u + 1))
      (BigPHSpaceOver.topology T Z) (BigPHSpaceOver.topology T X)
      (BigPHSpaceOver.topology T Y) ≪≫
    (bigPHMorphismPushforwardIso T (f ≫ g)).symm

/-- **Stacks 0DFP.** The inverse-image comparison is the adjunction mate of the direct-image
comparison. -/
@[stacks 0DFP "inverse-image composition"]
noncomputable def bigPHMorphism_comp_inverseImageIso :
    ((bigPHMorphism T g).comp (bigPHMorphism T f)).inverseImage ≅
      (bigPHMorphism T (f ≫ g)).inverseImage :=
  Adjunction.leftAdjointCompIso (bigPHMorphism T g).adj (bigPHMorphism T f).adj
    (bigPHMorphism T (f ≫ g)).adj (bigPHMorphism_comp_pushforwardIso T f g)

end Comp

end AlgebraicGeometry.BigPHSpaceSite

end
