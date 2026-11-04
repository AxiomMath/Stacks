module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleSite
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Localization.OverPullbackMorphism
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizationTriangle
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# Morphisms of big étale topoi of algebraic spaces (Stacks 0DF5)

A morphism `f : Y ⟶ X` of algebraic spaces in a big étale site of algebraic spaces induces a
morphism of the associated big étale topoi. Its inverse image is restriction along
composition with `f`, its direct image is computed by base change along `f`, and the inverse
image itself has a left adjoint which preserves fibre products and equalizers.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.bigEtaleMorphism` is the induced morphism of big étale
  topoi: **Stacks 0DF5**.
* `CategoryTheory.Functor.sheafPullback` is the left adjoint of its inverse image.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.bigEtaleLowerShriek_preservesPullbacks` and
  `AlgebraicGeometry.BigEtaleSpaceSite.bigEtaleLowerShriek_preservesEqualizers`: the
  exactness properties of that left adjoint.
* `CategoryTheory.Functor.sheafPushforwardContinuous_obj_obj_obj` computes the sections of
  the inverse image and `StacksRelocalization.sheafPushforwardObjEquiv` those
  of the direct image.
* `StacksRelocalization.sheafPushforwardOverMapIso` identifies the morphism of
  topoi induced by the cocontinuous composition functor with the one induced by its
  continuous base-change right adjoint.

## Implementation notes

The big étale site of an algebraic space `X` of the site is the localization at `X`, so its
underlying category is the slice `Over X` and the functors of the source are `Over.map f` and
`Over.pullback f`. Their adjunction, the cocontinuity of the first and the continuity of the
second are the general localization results, registered here for this site rather than
restated: `map_isCocontinuous`,
`StacksRelocalization.isMorphismOfSites_overPullback` and
`CategoryTheory.Over.mapPullbackAdj`.

With that, the morphism of topoi is assembled from the cocontinuous pushforward as direct
image and the continuous pushforward as inverse image, and the inverse-image formula of the
source holds definitionally. The comparison of the two descriptions of the direct image is an
isomorphism of pushforward functors, which also determines the inverse-image comparison.

Exactness of the left adjoint is `CategoryTheory.Functor.preservesLimitsOfShape_sheafPullback`
applied to `Over.map f`. Its hypotheses are that the slice categories have fibre products and
equalizers and that `Over.map f` preserves both: the slices have fibre products because the
category of algebraic spaces does (Tag 043C), hence binary products and so equalizers, and
`Over.map f` preserves any connected shape of limit because its composite with the forgetful
functor of the slice is the forgetful functor, which both preserves and reflects them.

## References

* [Stacks Project, Tag 0DF5](https://stacks.math.columbia.edu/tag/0DF5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

add_to_stacks 0DF5 "cocontinuity of the composition functor"
  map_isCocontinuous
add_to_stacks 0DF5 "continuous base-change right adjoint"
  StacksRelocalization.isMorphismOfSites_overPullback
add_to_stacks 0DF5 "adjunction of composition and base change"
  CategoryTheory.Over.mapPullbackAdj
add_to_stacks 0DF5 "comparison of the two morphisms of topoi"
  StacksRelocalization.sheafPushforwardOverMapIso
add_to_stacks 0DF5 "inverse-image comparison"
  StacksRelocalization.sheafPullbackOverPullbackIso
add_to_stacks 0DF5 "inverse-image formula"
  CategoryTheory.Functor.sheafPushforwardContinuous_obj_obj_obj
add_to_stacks 0DF5 "direct-image formula"
  StacksRelocalization.sheafPushforwardObjEquiv
add_to_stacks 0DF5 "existence of lower shriek"
  CategoryTheory.Functor.sheafAdjunctionContinuous

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) {X Y : T.Spaces} (f : Y ⟶ X)

/-- The slice of the category of algebraic spaces over an algebraic space has equalizers: it
has fibre products by Tag 043C, hence binary products, and those give equalizers. -/
noncomputable instance bigEtaleOver_hasEqualizers (X : T.Spaces) : HasEqualizers (Over X) :=
  have _ : HasBinaryProducts (Over X) := Over.ConstructProducts.over_binaryProduct_of_pullback
  hasEqualizers_of_hasPullbacks_and_binary_products

/-- Composition with `f` preserves limits of any connected shape, because its composite with
the forgetful functor of the slice is the forgetful functor, which preserves and reflects
them. -/
noncomputable instance overMap_preservesLimitsOfShape_of_isConnected
    {I : Type*} [SmallCategory I] [IsConnected I]
    [HasLimitsOfShape I (Over Y)] [HasLimitsOfShape I (Over X)] :
    PreservesLimitsOfShape I (Over.map f) :=
  have : PreservesLimitsOfShape I (Over.map f ⋙ Over.forget X) := by
    rw [Over.mapForget_eq]; infer_instance
  preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget X)

/-- **Stacks 0DF5.** The morphism of big étale topoi induced by a morphism of algebraic
spaces: its direct image is the cocontinuous pushforward along composition with `f` and its
inverse image is the continuous pushforward along the same functor, so sections of the
inverse image are given by `CategoryTheory.Functor.sheafPushforwardContinuous_obj_obj_obj`. -/
@[stacks 0DF5 "the morphism of big étale topoi and its inverse-image formula",
  sga "4 IV 4.7" "special case"]
noncomputable def bigEtaleMorphism :
    MorphismOfTopoi
      (Sheaf (T.bigEtaleTopology Y) (Type (u + 1)))
      (Sheaf (T.bigEtaleTopology X) (Type (u + 1))) where
  pushforward := (Over.map f).sheafPushforwardCocontinuous (Type (u + 1))
    (T.bigEtaleTopology Y) (T.bigEtaleTopology X)
  inverseImage := (Over.map f).sheafPushforwardContinuous (Type (u + 1))
    (T.bigEtaleTopology Y) (T.bigEtaleTopology X)
  adj := (Over.map f).sheafAdjunctionCocontinuous (Type (u + 1))
    (T.bigEtaleTopology Y) (T.bigEtaleTopology X)
  preservesFiniteLimits := inferInstance

/-- **Stacks 0DF5.** The left adjoint of the inverse image of
`AlgebraicGeometry.BigEtaleSpaceSite.bigEtaleMorphism` preserves fibre products. -/
@[stacks 0DF5 "lower shriek preserves fibre products"]
noncomputable instance bigEtaleLowerShriek_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan
      ((Over.map f).sheafPullback (Type (u + 1))
        (T.bigEtaleTopology Y) (T.bigEtaleTopology X)) :=
  Functor.preservesLimitsOfShape_sheafPullback (Over.map f)
    (T.bigEtaleTopology Y) (T.bigEtaleTopology X) (I := WalkingCospan)

/-- **Stacks 0DF5.** The left adjoint of the inverse image of
`AlgebraicGeometry.BigEtaleSpaceSite.bigEtaleMorphism` preserves equalizers. -/
@[stacks 0DF5 "lower shriek preserves equalizers"]
noncomputable instance bigEtaleLowerShriek_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair
      ((Over.map f).sheafPullback (Type (u + 1))
        (T.bigEtaleTopology Y) (T.bigEtaleTopology X)) :=
  Functor.preservesLimitsOfShape_sheafPullback (Over.map f)
    (T.bigEtaleTopology Y) (T.bigEtaleTopology X) (I := WalkingParallelPair)

end AlgebraicGeometry.BigEtaleSpaceSite

end
