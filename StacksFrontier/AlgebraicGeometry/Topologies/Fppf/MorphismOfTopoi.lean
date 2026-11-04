module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of big fppf topoi

A morphism `f : T ⟶ S` in a big fppf site induces a morphism from the big fppf topos over
`T` to the big fppf topos over `S`.  Postcomposition along `f` on the slice categories is
cocontinuous and continuous, and its right adjoint is base change, which is continuous.
The induced inverse and direct images are restriction along postcomposition and along base
change respectively, and the inverse image itself has a left adjoint, which preserves fibre
products and equalizers.

## Main definitions

* `AlgebraicGeometry.bigFppfMorphism`: the morphism of big fppf topoi induced by `f`.
* `AlgebraicGeometry.bigFppfLowerShriekAdjunction`: the left adjoint of its inverse image.

## Main results

* `AlgebraicGeometry.bigFppfLowerShriek_preservesPullbacks` and
  `AlgebraicGeometry.bigFppfLowerShriek_preservesEqualizers`: the left adjoint of the
  inverse image preserves fibre products and equalizers.

## Implementation notes

The big fppf category over a scheme is a slice category, so the continuity assertions are
instances of the general slice-site theorems rather than facts special to the fppf
topology, and the formulas for the sheaf images are the general comparison isomorphisms for
continuous and cocontinuous functors and for adjoint site functors.  The formulas on
sections are recorded as natural isomorphisms of sheaf functors, so they retain naturality
both in the sheaf and in the object.  The adjunction of site functors is
`CategoryTheory.Over.mapPullbackAdj`.

## References

* [Stacks Project, Tag 021W](https://stacks.math.columbia.edu/tag/021W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

add_to_stacks 021W "the postcomposition functor" CategoryTheory.Over.map
add_to_stacks 021W "the base-change functor" CategoryTheory.Over.pullback
add_to_stacks 021W "the base-change adjunction" CategoryTheory.Over.mapPullbackAdj
add_to_stacks 021W "cocontinuity of postcomposition"
  CategoryTheory.GrothendieckTopology.instIsCocontinuousOverMapOver
add_to_stacks 021W "continuity of postcomposition"
  CategoryTheory.GrothendieckTopology.instIsContinuousOverMapOver
add_to_stacks 021W "continuity of base change"
  CategoryTheory.GrothendieckTopology.instIsContinuousOverPullbackOver
add_to_stacks 021W "the inverse-image formula"
  CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous
add_to_stacks 021W "the direct-image formula"
  CategoryTheory.Adjunction.sheafPushforwardCocontinuousIso

/-- Postcomposition along a morphism preserves limits of any connected shape that both
slices admit: its composite with the slice-forgetful functor is the slice-forgetful
functor, which preserves and reflects such limits. -/
public instance overMap_preservesLimitsOfShape_of_isConnected
    {C : Type*} [Category C] {T S : C} (f : T ⟶ S)
    {I : Type*} [SmallCategory I] [IsConnected I]
    [HasLimitsOfShape I (Over T)] [HasLimitsOfShape I (Over S)] :
    PreservesLimitsOfShape I (Over.map f) := by
  have h : PreservesLimitsOfShape I ((Over.map f) ⋙ Over.forget S) := by
    rw [Over.mapForget_eq]
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget S)

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (T S : B.Schemes) (f : T ⟶ S)

include f

/-- A slice of the underlying category of a big fppf site has equalizers, since it has
fibre products and binary products. -/
private instance bigFppfOver_hasEqualizers (B : AlgebraicGeometry.BigFppfSite.{u})
    (X : B.Schemes) : HasEqualizers (Over X) := by
  let : HasBinaryProducts (Over X) := Over.ConstructProducts.over_binaryProduct_of_pullback
  exact hasEqualizers_of_hasPullbacks_and_binary_products

/-- Base change along `f`, sending `U / S` to the canonical fibre product `U ×_S T / T`, is
continuous for the big fppf topologies. The topology of the big fppf category over a scheme is
by construction the localization of the chosen big fppf topology at that scheme, so this is the
continuity of base change between localizations of one topology. -/
public instance bigFppfPullback_isContinuous :
    (Over.pullback f).IsContinuous
      (AlgebraicGeometry.BigFppfOver.topology B S.1 S.2)
      (AlgebraicGeometry.BigFppfOver.topology B T.1 T.2) :=
  inferInstanceAs ((Over.pullback f).IsContinuous (B.topology.over S) (B.topology.over T))

/-- **Stacks 021W.** The morphism of big fppf topoi induced by postcomposition along
`f`. -/
@[stacks 021W "the morphism of topoi"]
public noncomputable def bigFppfMorphism :
    MorphismOfTopoi
      (Sheaf (B.topology.over T) (Type (u + 1)))
      (Sheaf (B.topology.over S) (Type (u + 1))) :=
  { pushforward := (Over.map f).sheafPushforwardCocontinuous
      (Type (u + 1)) (B.topology.over T) (B.topology.over S)
    inverseImage := (Over.map f).sheafPullbackCocontinuous
      (Type (u + 1)) (B.topology.over T) (B.topology.over S)
    adj := (Over.map f).sheafAdjunctionPullbackCocontinuous
      (Type (u + 1)) (B.topology.over T) (B.topology.over S)
    preservesFiniteLimits := inferInstance }

/-- **Stacks 021W.** The left adjoint of the inverse image is sheaf pullback along
postcomposition. -/
@[stacks 021W "existence of lower shriek"]
public noncomputable def bigFppfLowerShriekAdjunction :
    (Over.map f).sheafPullback (Type (u + 1))
      (B.topology.over T) (B.topology.over S) ⊣
        (bigFppfMorphism B T S f).inverseImage :=
  ((Over.map f).sheafAdjunctionLowerShriek (Type (u + 1))
      (B.topology.over T) (B.topology.over S)).ofNatIsoLeft
      ((Functor.sheafPullbackConstruction.sheafPullbackIso (Over.map f)
        (Type (u + 1)) (B.topology.over T) (B.topology.over S)).symm) |>.ofNatIsoRight
      ((Over.map f).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
        (Type (u + 1)) (B.topology.over T) (B.topology.over S)).symm

/-- **Stacks 021W.** The left adjoint of the inverse image preserves fibre products. -/
@[stacks 021W "lower shriek preserves fibre products"]
public instance bigFppfLowerShriek_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan
      ((Over.map f).sheafPullback (Type (u + 1))
        (B.topology.over T) (B.topology.over S)) := by
  have hET := bigFppfOver_hasEqualizers B T
  have hES := bigFppfOver_hasEqualizers B S
  exact Functor.preservesLimitsOfShape_sheafPullback (Over.map f)
    (B.topology.over T) (B.topology.over S) (I := WalkingCospan)

/-- **Stacks 021W.** The left adjoint of the inverse image preserves equalizers. -/
@[stacks 021W "lower shriek preserves equalizers"]
public instance bigFppfLowerShriek_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair
      ((Over.map f).sheafPullback (Type (u + 1))
        (B.topology.over T) (B.topology.over S)) := by
  have hET := bigFppfOver_hasEqualizers B T
  have hES := bigFppfOver_hasEqualizers B S
  exact Functor.preservesLimitsOfShape_sheafPullback (Over.map f)
    (B.topology.over T) (B.topology.over S) (I := WalkingParallelPair)

end AlgebraicGeometry
