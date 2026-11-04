module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.MorphismOfTopoi
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.BigSite
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import StacksFrontier.CategoryTheory.Sites.CocontinuousRightAdjointMorphismOfSites
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of big ph topoi

A morphism `f : T ⟶ S` in a big ph site induces a morphism from the big ph topos over `T`
to the big ph topos over `S`.  Its inverse image is restriction along postcomposition and
its direct image is restriction along base change.  The inverse image has a left adjoint,
which preserves fibre products and equalizers.

## Main definitions

* `AlgebraicGeometry.bigPHMorphism`: the morphism of big ph topoi induced by `f`.
* `AlgebraicGeometry.bigPHLowerShriekAdjunction`: the left adjoint of its inverse image.

## Main results

* `AlgebraicGeometry.bigPHMorphismInverseImageIso` and
  `AlgebraicGeometry.bigPHMorphismPushforwardIso`: the formulas for the two images.
* `AlgebraicGeometry.bigPHLowerShriek_preservesPullbacks` and
  `AlgebraicGeometry.bigPHLowerShriek_preservesEqualizers`: exactness of the left adjoint.

## Implementation notes

The big ph category over a scheme is the slice of Stacks 0DBL.  The right adjoint of
postcomposition is `CategoryTheory.Over.pullback`, whose existence in the size-bounded
category rests on the fibre products of Stacks 021U; the continuity and cocontinuity of
both site functors are Mathlib's generic instances for slice topologies.  The formulas on
sections are stated as natural isomorphisms with restriction functors, so they stay natural
in both the sheaf and the object.  The morphism of topoi is presented by its inverse-image
and direct-image functors, and their agreement with the morphisms attached to the two site
functors is exactly what these isomorphisms record.

## References

* [Stacks Project, Tag 0DBR](https://stacks.math.columbia.edu/tag/0DBR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

add_to_stacks 0DBR "the postcomposition functor" CategoryTheory.Over.map
add_to_stacks 0DBR "the base-change functor" CategoryTheory.Over.pullback
add_to_stacks 0DBR "the base-change adjunction" CategoryTheory.Over.mapPullbackAdj

variable (B : BigPHSite.{u}) (T S : B.Schemes) (f : T ⟶ S)

include f

/-- A slice of the underlying category of a big ph site has equalizers, since it has fibre
products and binary products. -/
private instance bigPHOver_hasEqualizers (X : B.Schemes) : HasEqualizers (Over X) := by
  let : HasBinaryProducts (Over X) := Over.ConstructProducts.over_binaryProduct_of_pullback
  exact hasEqualizers_of_hasPullbacks_and_binary_products

/-- **Stacks 0DBR.** The morphism of big ph topoi induced by `f`. -/
@[stacks 0DBR "the morphism of topoi"]
public noncomputable def bigPHMorphism :
    MorphismOfTopoi
      (Sheaf (BigPHOver.topology B T.obj T.property) (Type (u + 1)))
      (Sheaf (BigPHOver.topology B S.obj S.property) (Type (u + 1))) := by
  let F := Over.map f
  let J := BigPHOver.topology B T.obj T.property
  let K := BigPHOver.topology B S.obj S.property
  have : F.IsContinuous J K := inferInstance
  have : F.IsCocontinuous J K := inferInstance
  exact
    { pushforward := F.sheafPushforwardCocontinuous (Type (u + 1)) J K
      inverseImage := F.sheafPullbackCocontinuous (Type (u + 1)) J K
      adj := F.sheafAdjunctionPullbackCocontinuous (Type (u + 1)) J K
      preservesFiniteLimits := inferInstance }

/-- **Stacks 0DBR.** Inverse image is restriction along postcomposition, naturally in
sheaves and objects. -/
@[stacks 0DBR "the inverse-image formula"]
public noncomputable def bigPHMorphismInverseImageIso :
    (bigPHMorphism B T S f).inverseImage ≅
      (Over.map f).sheafPushforwardContinuous (Type (u + 1))
        (BigPHOver.topology B T.obj T.property)
        (BigPHOver.topology B S.obj S.property) :=
  (Over.map f).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
    (Type (u + 1)) (BigPHOver.topology B T.obj T.property)
    (BigPHOver.topology B S.obj S.property)

/-- **Stacks 0DBR.** Direct image is restriction along base change, naturally in sheaves
and objects. -/
@[stacks 0DBR "the direct-image formula"]
public noncomputable def bigPHMorphismPushforwardIso :
    (bigPHMorphism B T S f).pushforward ≅
      (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (BigPHOver.topology B S.obj S.property)
        (BigPHOver.topology B T.obj T.property) :=
  (Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso (Type (u + 1))

/-- **Stacks 0DBR.** The lower shriek functor is left adjoint to inverse image. -/
@[stacks 0DBR "existence of lower shriek"]
public noncomputable def bigPHLowerShriekAdjunction :
    (Over.map f).sheafPullback (Type (u + 1))
      (BigPHOver.topology B T.obj T.property)
      (BigPHOver.topology B S.obj S.property) ⊣
        (bigPHMorphism B T S f).inverseImage :=
  (((Over.map f).sheafAdjunctionLowerShriek (Type (u + 1)) _ _).ofNatIsoLeft
    (Functor.sheafPullbackConstruction.sheafPullbackIso (Over.map f)
      (Type (u + 1)) _ _).symm).ofNatIsoRight
    (bigPHMorphismInverseImageIso B T S f).symm

/-- **Stacks 0DBR.** Lower shriek preserves fibre products. -/
@[stacks 0DBR "lower shriek preserves fibre products"]
public instance bigPHLowerShriek_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan
      ((Over.map f).sheafPullback (Type (u + 1))
        (BigPHOver.topology B T.obj T.property)
        (BigPHOver.topology B S.obj S.property)) := by
  have hET := bigPHOver_hasEqualizers B T
  have hES := bigPHOver_hasEqualizers B S
  exact Functor.preservesLimitsOfShape_sheafPullback
    (Over.map f) (BigPHOver.topology B T.obj T.property)
    (BigPHOver.topology B S.obj S.property) (I := WalkingCospan)

/-- **Stacks 0DBR.** Lower shriek preserves equalizers. -/
@[stacks 0DBR "lower shriek preserves equalizers"]
public instance bigPHLowerShriek_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair
      ((Over.map f).sheafPullback (Type (u + 1))
        (BigPHOver.topology B T.obj T.property)
        (BigPHOver.topology B S.obj S.property)) := by
  have hET := bigPHOver_hasEqualizers B T
  have hES := bigPHOver_hasEqualizers B S
  exact Functor.preservesLimitsOfShape_sheafPullback
    (Over.map f) (BigPHOver.topology B T.obj T.property)
    (BigPHOver.topology B S.obj S.property) (I := WalkingParallelPair)

end AlgebraicGeometry
