module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.MorphismOfTopoi
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExistence
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.SlicePost.Continuous
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import StacksFrontier.CategoryTheory.Sites.CocontinuousRightAdjointMorphismOfSites

/-!
# Morphisms of big étale topoi

A morphism `f : T ⟶ S` in a big étale site induces a functor from the big étale category over
`T` to the one over `S`, by composing structure morphisms with `f`. This functor is
cocontinuous, and it has a continuous right adjoint given by base change along `f`. The two
functors determine the *same* morphism from the big étale topos of `T` to that of `S`, so that
morphism can be described from either side:

* inverse image is restriction along composition, `f⁻¹(G)(U / T) ≅ G(U / S)`;
* direct image is restriction along base change, `f_*(F)(U / S) ≅ F(U ×_S T / T)`.

Since composition with `f` preserves fibre products and equalizers, the inverse image also has
a left adjoint `f_!`, itself left exact.

## Main definitions

* `CategoryTheory.Over.map` — composition with `f`.
* `CategoryTheory.Over.pullback` — its base-change right adjoint.
* `AlgebraicGeometry.bigEtaleMorphism` — the induced morphism of big étale topoi.

## Main results

* `AlgebraicGeometry.bigEtaleMap_isCocontinuous`,
  `AlgebraicGeometry.bigEtaleMap_isContinuous` and
  `AlgebraicGeometry.bigEtalePullback_isContinuous` — the continuity properties of
  composition and of base change.
* `AlgebraicGeometry.bigEtaleMorphismInverseImageIso` and
  `AlgebraicGeometry.bigEtaleMorphismPushforwardIso` — the two formulas on sections, which
  together say the two descriptions agree.
* `AlgebraicGeometry.bigEtaleLowerShriekAdjunction` — the lower shriek, with the two
  preservation instances giving its left exactness.

## Implementation notes

The big étale category over a scheme is a slice category, so composition, base change and
their adjunction are Mathlib's `Over.map`, `Over.pullback` and `Over.mapPullbackAdj`, and are
referenced rather than redefined. What makes those applicable is that the slice topology is the
localized topology, which is `bigEtaleOver_topology_eq`; each of the three continuity
statements is proved by rewriting along it and then appealing to the general slice instance.

The formulas on sections are recorded as natural isomorphisms with restriction functors rather
than as equalities of section sets, which keeps their naturality in both the sheaf and the
object. Following the treatment of morphisms of topoi elsewhere in the library, equality of the
two induced geometric morphisms is represented by the canonical isomorphism of their
direct-image functors.

## References

* [Stacks Project, Lemma 34.4.5 (Tag 021H)](https://stacks.math.columbia.edu/tag/021H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

add_to_stacks 021H "the postcomposition functor" CategoryTheory.Over.map
add_to_stacks 021H "the base-change functor" CategoryTheory.Over.pullback
add_to_stacks 021H "the base-change adjunction" CategoryTheory.Over.mapPullbackAdj

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

include f

/-- **Stacks 021H.** Composition with `f` is cocontinuous for the big étale topologies. -/
@[stacks 021H "cocontinuity"]
public instance bigEtaleMap_isCocontinuous :
    (Over.map f).IsCocontinuous
      (BigEtaleOver.topology B T.obj T.property)
      (BigEtaleOver.topology B S.obj S.property) := by
  rw [bigEtaleOver_topology_eq B T.obj T.property,
    bigEtaleOver_topology_eq B S.obj S.property]
  infer_instance

/-- Composition with `f` is also continuous.  This is the continuity used to identify inverse
image with restriction and to construct the lower shriek. -/
@[stacks 021H "continuity"]
public instance bigEtaleMap_isContinuous :
    (Over.map f).IsContinuous
      (BigEtaleOver.topology B T.obj T.property)
      (BigEtaleOver.topology B S.obj S.property) := by
  rw [bigEtaleOver_topology_eq B T.obj T.property,
    bigEtaleOver_topology_eq B S.obj S.property]
  infer_instance

/-- **Stacks 021H.** Pullback along `f`, sending `U / S` to the canonical fibre product
`U ×_S T / T`, is continuous for the big étale topologies. -/
@[stacks 021H "continuity of the base-change right adjoint"]
public instance bigEtalePullback_isContinuous :
    (Over.pullback f).IsContinuous
      (BigEtaleOver.topology B S.obj S.property)
      (BigEtaleOver.topology B T.obj T.property) := by
  rw [bigEtaleOver_topology_eq B S.obj S.property,
    bigEtaleOver_topology_eq B T.obj T.property]
  infer_instance

/-- **Stacks 021H.** The morphism of big étale topoi induced by the cocontinuous functor
`Over.map f`. -/
@[stacks 021H "the morphism of topoi"]
public noncomputable def bigEtaleMorphism (f : T ⟶ S) :
    MorphismOfTopoi
      (Sheaf (BigEtaleOver.topology B T.obj T.property) (Type (u + 1)))
      (Sheaf (BigEtaleOver.topology B S.obj S.property) (Type (u + 1))) := by
  let F := Over.map f
  have : F.IsCocontinuous
      (BigEtaleOver.topology B T.obj T.property)
      (BigEtaleOver.topology B S.obj S.property) := inferInstance
  exact
    { pushforward := F.sheafPushforwardCocontinuous (Type (u + 1))
        (BigEtaleOver.topology B T.obj T.property)
        (BigEtaleOver.topology B S.obj S.property)
      inverseImage := F.sheafPullbackCocontinuous (Type (u + 1))
        (BigEtaleOver.topology B T.obj T.property)
        (BigEtaleOver.topology B S.obj S.property)
      adj := F.sheafAdjunctionPullbackCocontinuous (Type (u + 1))
        (BigEtaleOver.topology B T.obj T.property)
        (BigEtaleOver.topology B S.obj S.property)
      preservesFiniteLimits := inferInstance }

/-- **Stacks 021H.** Inverse image is restriction along composition with `f`.  On an object
`U / T`, this is the formula `f_big⁻¹(G)(U / T) ≅ G(U / S)`. -/
@[stacks 021H "the inverse-image formula"]
public noncomputable def bigEtaleMorphismInverseImageIso :
    (bigEtaleMorphism B T S f).inverseImage ≅
      (Over.map f).sheafPushforwardContinuous (Type (u + 1))
        (BigEtaleOver.topology B T.obj T.property)
        (BigEtaleOver.topology B S.obj S.property) :=
  (Over.map f).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
    (Type (u + 1)) (BigEtaleOver.topology B T.obj T.property)
    (BigEtaleOver.topology B S.obj S.property)

/-- **Stacks 021H.** Direct image is restriction along base change.  On an object `U / S`,
this is the formula `f_big,*(F)(U / S) ≅ F(U ×_S T / T)`. -/
@[stacks 021H "the direct-image formula"]
public noncomputable def bigEtaleMorphismPushforwardIso :
    (bigEtaleMorphism B T S f).pushforward ≅
      (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (BigEtaleOver.topology B S.obj S.property)
        (BigEtaleOver.topology B T.obj T.property) := by
  let adj := Over.mapPullbackAdj f
  exact adj.sheafPushforwardCocontinuousIso (Type (u + 1))

/-- **Stacks 021H.** The inverse-image functor has the sheaf pullback along postcomposition
as a left adjoint; this is `f_big!`. -/
@[stacks 021H "existence of lower shriek"]
public noncomputable def bigEtaleLowerShriekAdjunction :
    (Over.map f).sheafPullback (Type (u + 1))
      (BigEtaleOver.topology B T.obj T.property)
      (BigEtaleOver.topology B S.obj S.property) ⊣
        (bigEtaleMorphism B T S f).inverseImage := by
  exact (((Over.map f).sheafAdjunctionLowerShriek (Type (u + 1))
      (BigEtaleOver.topology B T.obj T.property)
      (BigEtaleOver.topology B S.obj S.property)).ofNatIsoLeft
        (Functor.sheafPullbackConstruction.sheafPullbackIso (Over.map f) (Type (u + 1))
          (BigEtaleOver.topology B T.obj T.property)
          (BigEtaleOver.topology B S.obj S.property)).symm).ofNatIsoRight
    (bigEtaleMorphismInverseImageIso B T S f).symm

/-- **Stacks 021H.** The lower shriek commutes with fibre products. -/
@[stacks 021H "lower shriek preserves fibre products"]
public instance bigEtaleLowerShriek_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan
      ((Over.map f).sheafPullback (Type (u + 1))
        (BigEtaleOver.topology B T.obj T.property)
        (BigEtaleOver.topology B S.obj S.property)) := by
  have : HasEqualizers (Over T) := bigEtaleOver_hasEqualizers B T
  have : HasEqualizers (Over S) := bigEtaleOver_hasEqualizers B S
  exact Functor.preservesLimitsOfShape_sheafPullback
    (Over.map f) (BigEtaleOver.topology B T.obj T.property)
    (BigEtaleOver.topology B S.obj S.property)
    (I := WalkingCospan)

/-- **Stacks 021H.** The lower shriek commutes with equalizers. -/
@[stacks 021H "lower shriek preserves equalizers"]
public instance bigEtaleLowerShriek_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair
      ((Over.map f).sheafPullback (Type (u + 1))
        (BigEtaleOver.topology B T.obj T.property)
        (BigEtaleOver.topology B S.obj S.property)) := by
  have : HasEqualizers (Over T) := bigEtaleOver_hasEqualizers B T
  have : HasEqualizers (Over S) := bigEtaleOver_hasEqualizers B S
  exact Functor.preservesLimitsOfShape_sheafPullback
    (Over.map f) (BigEtaleOver.topology B T.obj T.property)
    (BigEtaleOver.topology B S.obj S.property)
    (I := WalkingParallelPair)

end AlgebraicGeometry
