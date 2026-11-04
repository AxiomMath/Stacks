module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.BigSiteOver
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizationTriangle
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# Morphisms of big syntomic topoi

A morphism `f : T ⟶ S` in a big syntomic site induces, by composing structure morphisms with
`f`, a functor between the localized big syntomic sites. That functor is cocontinuous, and it
has a continuous right adjoint given by base change along `f`. The two determine the *same*
morphism of topoi, so it can be described from either side:

* inverse image is restriction along composition, `f⁻¹(G)(U / T) ≅ G(U / S)`;
* direct image is restriction along base change, `f_*(F)(U / S) ≅ F(U ×_S T / T)`.

Since composition with `f` preserves fibre products and equalizers, the inverse image also has
a left adjoint `f_!`, itself left exact.

## Main definitions

* `AlgebraicGeometry.bigSyntomicMorphismOfTopoi` — the induced morphism of big syntomic topoi.

## Main results

* `AlgebraicGeometry.bigSyntomicMorphismPushforwardIso` — the two descriptions agree.
* `AlgebraicGeometry.bigSyntomicLowerShriekAdjunction` — the lower shriek, with the two
  preservation instances giving its left exactness.

## Implementation notes

The big syntomic site over an object is its slice category with the localized topology, so
composition, base change and their adjunction are Mathlib's `CategoryTheory.Over.map`,
`CategoryTheory.Over.pullback` and `CategoryTheory.Over.mapPullbackAdj`, and are referenced
rather than redefined; cocontinuity and the continuity of base change are the corresponding
general instances for a localized topology. What has to be supplied is that the cutoff category
underlying a big syntomic site has the fibre products those results need, which follows from
the size cutoff being closed under them.

Equality of the two induced geometric morphisms is represented by the canonical isomorphism of
their direct-image functors, inverse images being left adjoints and hence canonically
isomorphic as well.

## References

* [Stacks Project, Tag 04HD](https://stacks.math.columbia.edu/tag/04HD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

add_to_stacks 04HD "cocontinuity"
  CategoryTheory.GrothendieckTopology.instIsCocontinuousOverMapOver

add_to_stacks 04HD "right_adjoint" CategoryTheory.Over.mapPullbackAdj
add_to_stacks 04HD "right_adjoint"
  CategoryTheory.GrothendieckTopology.instIsContinuousOverPullbackOver

add_to_stacks 04HD "inverse_image"
  CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous

add_to_stacks 04HD "direct_image"
  CategoryTheory.Functor.sheafPushforwardCocontinuousIsoRestriction

/-- The cutoff category underlying a big syntomic site has fibre products. -/
private instance bigSyntomicSite_hasPullbacks (B : BigSyntomicSite.{u}) :
    HasPullbacks B.category :=
  inferInstance

/-- A slice of the cutoff category underlying a big syntomic site has equalizers. -/
private instance bigSyntomicOver_hasEqualizers (B : BigSyntomicSite.{u})
    (X : B.category) : HasEqualizers (Over X) := by
  have : HasPullbacks (Over X) := inferInstance
  have : HasBinaryProducts (Over X) := Over.ConstructProducts.over_binaryProduct_of_pullback
  exact hasEqualizers_of_hasPullbacks_and_binary_products

variable (B : BigSyntomicSite.{u}) {T S : B.category} (f : T ⟶ S)

private instance bigSyntomicOverMap_preservesLimitsOfConnectedShape
    {I : Type*} [SmallCategory I] [IsConnected I]
    [HasLimitsOfShape I (Over T)] [HasLimitsOfShape I (Over S)] :
    PreservesLimitsOfShape I (Over.map f) := by
  have h : PreservesLimitsOfShape I ((Over.map f) ⋙ Over.forget S) := by
    rw [Over.mapForget_eq]
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget S)

/-- Postcomposition between the two big syntomic slices is continuous. -/
private instance bigSyntomicOverMap_isContinuous :
    (Over.map f).IsContinuous
      (BigSyntomicOver.topology B T.obj T.property)
      (BigSyntomicOver.topology B S.obj S.property) := by
  simpa [BigSyntomicOver.topology] using
    (inferInstance : (Over.map f).IsContinuous (B.topology.over T) (B.topology.over S))

/-- **Stacks Project, Tag 04HD.** The big syntomic morphism of topoi attached
to `f : T ⟶ S` in a chosen big syntomic site. Its defining functor sends
`V ⟶ T` to the composite `V ⟶ T ⟶ S`. -/
@[stacks 04HD "big_syntomic_morphism", implicit_reducible, simps inverseImage pushforward]
public noncomputable def bigSyntomicMorphismOfTopoi : MorphismOfTopoi
    (Sheaf (BigSyntomicOver.topology B T.obj T.property) (Type (u + 1)))
    (Sheaf (BigSyntomicOver.topology B S.obj S.property) (Type (u + 1))) := by
  let F := Over.map f
  have : F.IsCocontinuous (BigSyntomicOver.topology B T.obj T.property)
      (BigSyntomicOver.topology B S.obj S.property) := inferInstance
  exact
    { pushforward := F.sheafPushforwardCocontinuous (Type (u + 1))
        (BigSyntomicOver.topology B T.obj T.property)
        (BigSyntomicOver.topology B S.obj S.property)
      inverseImage := F.sheafPullbackCocontinuous (Type (u + 1))
        (BigSyntomicOver.topology B T.obj T.property)
        (BigSyntomicOver.topology B S.obj S.property)
      adj := F.sheafAdjunctionPullbackCocontinuous (Type (u + 1))
        (BigSyntomicOver.topology B T.obj T.property)
        (BigSyntomicOver.topology B S.obj S.property)
      preservesFiniteLimits := inferInstance }

/-- **Stacks Project, Tag 04HD.** The big syntomic morphism of topoi defined by postcomposition
along `f` is the morphism of topoi induced by the continuous base-change functor
`Over.pullback f`: their direct images are canonically isomorphic. -/
@[stacks 04HD "same_morphism"]
public noncomputable def bigSyntomicMorphismPushforwardIso :
    (bigSyntomicMorphismOfTopoi B f).pushforward ≅
      (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (BigSyntomicOver.topology B S.obj S.property)
        (BigSyntomicOver.topology B T.obj T.property) :=
  (Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso (Type (u + 1))

/-- **Stacks Project, Tag 04HD.** The lower shriek on big syntomic sheaves is left adjoint to
inverse image. -/
@[stacks 04HD "lower_shriek"]
public noncomputable def bigSyntomicLowerShriekAdjunction :
    (Over.map f).sheafPullback (Type (u + 1))
      (BigSyntomicOver.topology B T.obj T.property)
      (BigSyntomicOver.topology B S.obj S.property) ⊣
        (bigSyntomicMorphismOfTopoi B f).inverseImage :=
  (((Over.map f).sheafAdjunctionLowerShriek (Type (u + 1))
      (BigSyntomicOver.topology B T.obj T.property)
      (BigSyntomicOver.topology B S.obj S.property)).ofNatIsoLeft
    (Functor.sheafPullbackConstruction.sheafPullbackIso (Over.map f) (Type (u + 1))
      (BigSyntomicOver.topology B T.obj T.property)
      (BigSyntomicOver.topology B S.obj S.property)).symm).ofNatIsoRight
    ((Over.map f).sheafPullbackCocontinuousIsoSheafPushforwardContinuous (Type (u + 1))
      (BigSyntomicOver.topology B T.obj T.property)
      (BigSyntomicOver.topology B S.obj S.property)).symm

/-- **Stacks Project, Tag 04HD.** The lower shriek preserves fibre products. -/
@[stacks 04HD "lower_shriek", instance]
public theorem bigSyntomicLowerShriek_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan
      ((Over.map f).sheafPullback (Type (u + 1))
        (BigSyntomicOver.topology B T.obj T.property)
        (BigSyntomicOver.topology B S.obj S.property)) :=
  Functor.preservesLimitsOfShape_sheafPullback
    (Over.map f) (BigSyntomicOver.topology B T.obj T.property)
    (BigSyntomicOver.topology B S.obj S.property) (I := WalkingCospan)

/-- **Stacks Project, Tag 04HD.** The lower shriek preserves equalizers. -/
@[stacks 04HD "lower_shriek", instance]
public theorem bigSyntomicLowerShriek_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair
      ((Over.map f).sheafPullback (Type (u + 1))
        (BigSyntomicOver.topology B T.obj T.property)
        (BigSyntomicOver.topology B S.obj S.property)) :=
  Functor.preservesLimitsOfShape_sheafPullback
    (Over.map f) (BigSyntomicOver.topology B T.obj T.property)
    (BigSyntomicOver.topology B S.obj S.property) (I := WalkingParallelPair)

end AlgebraicGeometry
