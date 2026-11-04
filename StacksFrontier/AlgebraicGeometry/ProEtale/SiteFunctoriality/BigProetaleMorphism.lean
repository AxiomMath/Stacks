module

public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SiteFunctorLimits
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of big pro-étale topoi

A morphism `f : T ⟶ S` in a chosen big pro-étale site induces a morphism between the topoi of
its big slices. Composition of structure maps is cocontinuous and has continuous base change as
a right adjoint, so inverse and direct image are given on sections by composition and by base
change respectively, and inverse image again has a left adjoint preserving fibre products and
equalizers.

## Main definitions

* `CategoryTheory.Over.map` — composition of structure morphisms.
* `CategoryTheory.Over.pullback` — base change.
* `AlgebraicGeometry.ProEtale.bigProetaleMorphism` — the induced geometric morphism.
* Sheaf pullback along `CategoryTheory.Over.map` — the left adjoint of inverse image, whose
  adjunction is `AlgebraicGeometry.ProEtale.bigProetaleLowerShriekAdjunction`.

## Main results

* The two functors are adjoint, and the general slice-site instances give cocontinuity of
  composition and continuity of both composition and base change.
* The geometric morphism has the canonical objectwise formulas for inverse and direct image.
* `AlgebraicGeometry.ProEtale.bigProetaleLowerShriek_preservesPullbacks` and
  `AlgebraicGeometry.ProEtale.bigProetaleLowerShriek_preservesEqualizers`.

## Implementation notes

The section formulas are expressed by natural isomorphisms rather than literal equality:
inverse image is identified with restriction along composition, and direct image with
restriction along base change. The geometric morphism is built from the cocontinuous functor,
and its agreement with the morphism induced by the continuous right adjoint is the natural
isomorphism `CategoryTheory.Adjunction.sheafPushforwardCocontinuousIso` between their
direct-image functors. The continuity assertions use the general slice-site instances rather
than instances specific to the pro-étale topology.

## References

* [Stacks Project, Tag 098S](https://stacks.math.columbia.edu/tag/098S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

add_to_stacks 098S "the composition functor" CategoryTheory.Over.map
add_to_sga "3 I 1.6" CategoryTheory.Over.map
add_to_sga "4 IV 5.5" CategoryTheory.Over.map
add_to_ega "I 2.5.3" CategoryTheory.Over.map
add_to_ega "I 2.5.4" "more general" CategoryTheory.Over.map
add_to_stacks 098S "the base-change functor" CategoryTheory.Over.pullback
add_to_sga "3 I 1.6" CategoryTheory.Over.pullback
add_to_sga "4 III 5.5" CategoryTheory.Over.pullback
add_to_sga "4 IV 5.2" "more general" CategoryTheory.Over.pullback
add_to_sga "4 IV 5.5" CategoryTheory.Over.pullback
add_to_ega "I 3.3.7" "more general" CategoryTheory.Over.pullback
add_to_ega "IV 8.2.6" CategoryTheory.Over.pullback
add_to_stacks 098S "the adjunction" CategoryTheory.Over.mapPullbackAdj
add_to_stacks 098S "cocontinuity of composition"
  CategoryTheory.GrothendieckTopology.instIsCocontinuousOverMapOver
add_to_stacks 098S "continuity of composition"
  CategoryTheory.GrothendieckTopology.instIsContinuousOverMapOver
add_to_stacks 098S "continuity of base change"
  CategoryTheory.GrothendieckTopology.instIsContinuousOverPullbackOver
add_to_stacks 098S "inverse-image formula"
  CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous
add_to_stacks 098S "direct-image formula and agreement of the two site functors"
  CategoryTheory.Adjunction.sheafPushforwardCocontinuousIso

/-- The geometric morphism of big pro-étale topoi induced by `f`. -/
@[stacks 098S "the morphism of topoi"]
public noncomputable def bigProetaleMorphism :
    MorphismOfTopoi
      (Sheaf (BigProetaleOver.topology B T.obj T.property) (Type (u + 1)))
      (Sheaf (BigProetaleOver.topology B S.obj S.property) (Type (u + 1))) :=
  { pushforward := (Over.map f).sheafPushforwardCocontinuous
      (Type (u + 1)) (BigProetaleOver.topology B T.obj T.property)
      (BigProetaleOver.topology B S.obj S.property)
    inverseImage := (Over.map f).sheafPullbackCocontinuous
      (Type (u + 1)) (BigProetaleOver.topology B T.obj T.property)
      (BigProetaleOver.topology B S.obj S.property)
    adj := (Over.map f).sheafAdjunctionPullbackCocontinuous
      (Type (u + 1)) (BigProetaleOver.topology B T.obj T.property)
      (BigProetaleOver.topology B S.obj S.property)
    preservesFiniteLimits := by infer_instance }

/-- Lower shriek is left adjoint to inverse image. -/
@[stacks 098S "existence of lower shriek"]
public noncomputable def bigProetaleLowerShriekAdjunction :
    (Over.map f).sheafPullback (Type (u + 1))
      (BigProetaleOver.topology B T.obj T.property)
      (BigProetaleOver.topology B S.obj S.property) ⊣
        (bigProetaleMorphism B T S f).inverseImage :=
  (((Over.map f).sheafAdjunctionLowerShriek (Type (u + 1))
      (BigProetaleOver.topology B T.obj T.property)
      (BigProetaleOver.topology B S.obj S.property)).ofNatIsoLeft
      (Functor.sheafPullbackConstruction.sheafPullbackIso (Over.map f)
        (Type (u + 1)) (BigProetaleOver.topology B T.obj T.property)
        (BigProetaleOver.topology B S.obj S.property)).symm).ofNatIsoRight
    ((Over.map f).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
      (Type (u + 1)) (BigProetaleOver.topology B T.obj T.property)
      (BigProetaleOver.topology B S.obj S.property)).symm

/-- Lower shriek preserves fibre products. -/
@[stacks 098S "lower shriek preserves fibre products"]
public instance bigProetaleLowerShriek_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan
      ((Over.map f).sheafPullback (Type (u + 1))
        (BigProetaleOver.topology B T.obj T.property)
        (BigProetaleOver.topology B S.obj S.property)) :=
  Functor.preservesLimitsOfShape_sheafPullback (Over.map f)
    (BigProetaleOver.topology B T.obj T.property)
    (BigProetaleOver.topology B S.obj S.property) (I := WalkingCospan)

/-- Lower shriek preserves equalizers. -/
@[stacks 098S "lower shriek preserves equalizers"]
public instance bigProetaleLowerShriek_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair
      ((Over.map f).sheafPullback (Type (u + 1))
        (BigProetaleOver.topology B T.obj T.property)
        (BigProetaleOver.topology B S.obj S.property)) :=
  Functor.preservesLimitsOfShape_sheafPullback (Over.map f)
    (BigProetaleOver.topology B T.obj T.property)
    (BigProetaleOver.topology B S.obj S.property) (I := WalkingParallelPair)

end AlgebraicGeometry.ProEtale

end
