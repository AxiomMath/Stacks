module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.BigSiteOver
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizationTriangle
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# Morphisms of big smooth topoi

A morphism `f : T ⟶ S` in a big smooth site induces, by composing structure morphisms with `f`,
a cocontinuous functor between the localized big smooth sites, hence a morphism of topoi. Base
change along `f` is a continuous right adjoint to that functor, and the morphism of topoi it
induces is the same one, so the morphism can be described from either side:

* inverse image is restriction along composition, `f⁻¹(G)(U / T) ≅ G(U / S)`;
* direct image is restriction along base change, `f_*(F)(U / S) ≅ F(U ×_S T / T)`.

The inverse image also has a left adjoint `f_!`, which preserves fibre products and equalizers.

## Main definitions

* `AlgebraicGeometry.bigSmoothMorphismOfTopoi` — the induced morphism of big smooth topoi.

## Main results

* `AlgebraicGeometry.bigSmoothOverMap_isCocontinuous` and
  `AlgebraicGeometry.bigSmoothOverMap_isContinuous` — composition with `f` is cocontinuous and
  continuous.
* `AlgebraicGeometry.bigSmoothOverMapPullbackAdj` and
  `AlgebraicGeometry.bigSmoothOverPullback_isContinuous` — base change along `f` is a continuous
  right adjoint of it.
* `AlgebraicGeometry.bigSmoothMorphismOfTopoiPushforwardIso`,
  `AlgebraicGeometry.bigSmoothMorphismOfTopoiPullbackAdjunction` and
  `AlgebraicGeometry.bigSmoothMorphismOfTopoiInverseImageIso` — the two descriptions agree, on
  direct images and on inverse images.
* `AlgebraicGeometry.bigSmoothInverseImageObjIso` and
  `AlgebraicGeometry.bigSmoothPushforwardObjIso` — the formulas on sections.
* `AlgebraicGeometry.bigSmoothInverseImage_isRightAdjoint` — the lower shriek exists.
* `AlgebraicGeometry.bigSmoothLowerShriek_preservesPullbacks` and
  `AlgebraicGeometry.bigSmoothLowerShriek_preservesEqualizers` — its preservation properties.

## Implementation notes

The big smooth site over an object is its slice category with the localized topology, so
composition and base change are Mathlib's `CategoryTheory.Over.map` and
`CategoryTheory.Over.pullback`, and cocontinuity, the adjunction and the continuity of base
change are the corresponding general results, instantiated at the two localized topologies.

Agreement of the two induced morphisms of topoi is expressed twice: as a natural isomorphism of
their direct images, and — by uniqueness of left adjoints — as a natural isomorphism of their
inverse images, the inverse image on the base-change side being the left adjoint of restriction
along base change.

The lower shriek is the chosen `CategoryTheory.Functor.leftAdjoint` of the inverse-image
functor, and the two preservation claims are the classes `PreservesLimitsOfShape WalkingCospan`
and `PreservesLimitsOfShape WalkingParallelPair` for it. Both hold unconditionally: composition
with `f` preserves all connected limits the two slices admit, fibre products and equalizers
among them.

Every statement here is for an arbitrary morphism `f` of the site; no monomorphism hypothesis is
needed, since the preservation of connected limits that both limit clauses rest on does not use
one.

## References

* [Stacks Project, Tag 04HC](https://stacks.math.columbia.edu/tag/04HC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

add_to_stacks 04HC "direct_image"
  CategoryTheory.Functor.sheafPushforwardCocontinuousIsoRestriction

add_to_stacks 04HC "inverse_image"
  CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous

/-- A slice of the cutoff category underlying a big smooth site has equalizers. -/
private instance bigSmoothOver_hasEqualizers (B : BigSmoothSite.{u}) (X : B.category) :
    HasEqualizers (Over X) := by
  have : HasPullbacks B.category := schemeCutoff_hasPullbacks B
  have : HasBinaryProducts (Over X) := Over.ConstructProducts.over_binaryProduct_of_pullback
  exact hasEqualizers_of_hasPullbacks_and_binary_products

private instance bigSmoothOverMap_preservesLimitsOfConnectedShape
    (B : BigSmoothSite.{u}) {T S : B.category} (f : T ⟶ S)
    {I : Type*} [SmallCategory I] [IsConnected I]
    [HasLimitsOfShape I (Over T)] [HasLimitsOfShape I (Over S)] :
    PreservesLimitsOfShape I (Over.map f) := by
  have h : PreservesLimitsOfShape I ((Over.map f) ⋙ Over.forget S) := by
    rw [Over.mapForget_eq]
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget S)

/-- The functor `V / T ↦ V / S` between the big smooth sites over `T` and over `S`, given by
composing the structure morphism with `f`, is cocontinuous. -/
@[stacks 04HC "cocontinuity"]
public instance bigSmoothOverMap_isCocontinuous
    (B : BigSmoothSite.{u}) {T S : B.category} (f : T ⟶ S) :
    (Over.map f).IsCocontinuous
      (BigSmoothOver.topology B T.obj T.property)
      (BigSmoothOver.topology B S.obj S.property) :=
  inferInstance

/-- The functor `V / T ↦ V / S` between the big smooth sites over `T` and over `S` is
continuous. -/
@[stacks 04HC "continuity"]
public instance bigSmoothOverMap_isContinuous
    (B : BigSmoothSite.{u}) {T S : B.category} (f : T ⟶ S) :
    (Over.map f).IsContinuous
      (BigSmoothOver.topology B T.obj T.property)
      (BigSmoothOver.topology B S.obj S.property) :=
  inferInstance

/-- Base change along `f`, the functor `(U → S) ↦ (U ×_S T → T)` between the big smooth sites
over `S` and over `T`, is right adjoint to composition with `f`. -/
@[stacks 04HC "continuous_right_adjoint"]
public noncomputable def bigSmoothOverMapPullbackAdj
    (B : BigSmoothSite.{u}) {T S : B.category} (f : T ⟶ S) :
    (Over.map f : BigSmoothOver B T.obj T.property ⥤ BigSmoothOver B S.obj S.property) ⊣
      Over.pullback f :=
  Over.mapPullbackAdj f

/-- Base change along `f` is continuous for the two localized big smooth topologies. -/
@[stacks 04HC "continuous_right_adjoint"]
public instance bigSmoothOverPullback_isContinuous
    (B : BigSmoothSite.{u}) {T S : B.category} (f : T ⟶ S) :
    (Over.pullback f).IsContinuous
      (BigSmoothOver.topology B S.obj S.property)
      (BigSmoothOver.topology B T.obj T.property) :=
  inferInstance

/-- The big smooth morphism of topoi associated to a morphism `f : T ⟶ S` in a big smooth site,
induced by the cocontinuous functor sending `V ⟶ T` to the composite `V ⟶ T ⟶ S`. -/
@[stacks 04HC "big_smooth_morphism_of_topoi", implicit_reducible]
public noncomputable def bigSmoothMorphismOfTopoi
    (B : BigSmoothSite.{u}) {T S : B.category} (f : T ⟶ S) :
    MorphismOfTopoi
      (Sheaf (BigSmoothOver.topology B T.obj T.property) (Type (u + 1)))
      (Sheaf (BigSmoothOver.topology B S.obj S.property) (Type (u + 1))) := by
  let F := Over.map f
  have : F.IsCocontinuous (BigSmoothOver.topology B T.obj T.property)
      (BigSmoothOver.topology B S.obj S.property) := inferInstance
  exact
    { pushforward := F.sheafPushforwardCocontinuous (Type (u + 1))
        (BigSmoothOver.topology B T.obj T.property)
        (BigSmoothOver.topology B S.obj S.property)
      inverseImage := F.sheafPullbackCocontinuous (Type (u + 1))
        (BigSmoothOver.topology B T.obj T.property)
        (BigSmoothOver.topology B S.obj S.property)
      adj := F.sheafAdjunctionPullbackCocontinuous (Type (u + 1))
        (BigSmoothOver.topology B T.obj T.property)
        (BigSmoothOver.topology B S.obj S.property)
      preservesFiniteLimits := inferInstance }

/-- The direct image of the big smooth morphism of topoi attached to postcomposition along `f`
is isomorphic to the direct image along the continuous base-change functor `Over.pullback f`. -/
@[stacks 04HC "agreement"]
public noncomputable def bigSmoothMorphismOfTopoiPushforwardIso
    (B : BigSmoothSite.{u}) {T S : B.category} (f : T ⟶ S) :
    (bigSmoothMorphismOfTopoi B f).pushforward ≅
      (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (BigSmoothOver.topology B S.obj S.property)
        (BigSmoothOver.topology B T.obj T.property) :=
  (Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso (Type (u + 1))

/-- The inverse image of the big smooth morphism of topoi is left adjoint to restriction along
base change. -/
@[stacks 04HC "agreement"]
public noncomputable def bigSmoothMorphismOfTopoiPullbackAdjunction
    (B : BigSmoothSite.{u}) {T S : B.category} (f : T ⟶ S) :
    (bigSmoothMorphismOfTopoi B f).inverseImage ⊣
      (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (BigSmoothOver.topology B S.obj S.property)
        (BigSmoothOver.topology B T.obj T.property) :=
  (bigSmoothMorphismOfTopoi B f).adj.ofNatIsoRight (bigSmoothMorphismOfTopoiPushforwardIso B f)

/-- The direct image of the morphism of topoi induced by base change along `f` has a left
adjoint, namely the inverse image of the big smooth morphism of topoi. -/
public noncomputable instance bigSmoothPushforwardPullback_isRightAdjoint
    (B : BigSmoothSite.{u}) {T S : B.category} (f : T ⟶ S) :
    ((Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
      (BigSmoothOver.topology B S.obj S.property)
      (BigSmoothOver.topology B T.obj T.property)).IsRightAdjoint :=
  (bigSmoothMorphismOfTopoiPullbackAdjunction B f).isRightAdjoint

/-- The inverse image of the big smooth morphism of topoi is isomorphic to the left adjoint of
restriction along base change. -/
@[stacks 04HC "agreement"]
public noncomputable def bigSmoothMorphismOfTopoiInverseImageIso
    (B : BigSmoothSite.{u}) {T S : B.category} (f : T ⟶ S) :
    (bigSmoothMorphismOfTopoi B f).inverseImage ≅
      ((Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (BigSmoothOver.topology B S.obj S.property)
        (BigSmoothOver.topology B T.obj T.property)).leftAdjoint :=
  Adjunction.leftAdjointUniq (bigSmoothMorphismOfTopoiPullbackAdjunction B f)
    (Adjunction.ofIsRightAdjoint _)

/-- The sections of an inverse image on `U / T` are the sections of the sheaf on `U / S`:
`f⁻¹(G)(U / T) = G(U / S)`. -/
@[stacks 04HC "inverse_image"]
public noncomputable def bigSmoothInverseImageObjIso
    (B : BigSmoothSite.{u}) {T S : B.category} (f : T ⟶ S)
    (G : Sheaf (BigSmoothOver.topology B S.obj S.property) (Type (u + 1))) (U : Over T) :
    ((bigSmoothMorphismOfTopoi B f).inverseImage.obj G).obj.obj (Opposite.op U) ≅
      G.obj.obj (Opposite.op (Over.mk (U.hom ≫ f))) :=
  (Over.map f).sheafPullbackCocontinuousObjObjIso (Type (u + 1))
    (BigSmoothOver.topology B T.obj T.property)
    (BigSmoothOver.topology B S.obj S.property) G U

/-- The sections of a direct image on `U / S` are the sections of the sheaf on the base change
`U ×_S T / T`: `f_*(F)(U / S) = F(U ×_S T / T)`. -/
@[stacks 04HC "direct_image"]
public noncomputable def bigSmoothPushforwardObjIso
    (B : BigSmoothSite.{u}) {T S : B.category} (f : T ⟶ S)
    (F : Sheaf (BigSmoothOver.topology B T.obj T.property) (Type (u + 1))) (U : Over S) :
    ((bigSmoothMorphismOfTopoi B f).pushforward.obj F).obj.obj (Opposite.op U) ≅
      F.obj.obj (Opposite.op (Over.mk (pullback.snd U.hom f))) :=
  ((Functor.sheafPushforwardCocontinuousIsoRestriction (Type (u + 1))
    (BigSmoothOver.topology B T.obj T.property)
    (BigSmoothOver.topology B S.obj S.property)
    (Over.mapPullbackAdj f)).app F).app (Opposite.op U)

/-- The inverse image of a big smooth morphism of topoi has a left adjoint. -/
@[stacks 04HC "left_adjoint"]
public noncomputable instance bigSmoothInverseImage_isRightAdjoint
    (B : BigSmoothSite.{u}) {T S : B.category} (f : T ⟶ S) :
    (bigSmoothMorphismOfTopoi B f).inverseImage.IsRightAdjoint :=
  (((Over.map f).sheafAdjunctionLowerShriek (Type (u + 1)) _ _).ofNatIsoRight
    ((Over.map f).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
      (Type (u + 1)) _ _).symm).isRightAdjoint

/-- The lower shriek of a big smooth morphism of topoi preserves every connected finite limit
shape for which the two slices have limits. -/
private theorem bigSmoothLowerShriekShape
    (B : BigSmoothSite.{u}) {T S : B.category} (f : T ⟶ S)
    {I : Type*} [SmallCategory I] [FinCategory I] [IsConnected I]
    [HasLimitsOfShape I (Over T)] [HasLimitsOfShape I (Over S)] :
    PreservesLimitsOfShape I
      (bigSmoothMorphismOfTopoi B f).inverseImage.leftAdjoint := by
  let F := Over.map f
  let J := BigSmoothOver.topology B T.obj T.property
  let K := BigSmoothOver.topology B S.obj S.property
  have : F.IsContinuous J K := bigSmoothOverMap_isContinuous B f
  have : PreservesLimitsOfShape I (F.sheafPullback (Type (u + 1)) J K) :=
    Functor.preservesLimitsOfShape_sheafPullback F J K (I := I)
  let i : (bigSmoothMorphismOfTopoi B f).inverseImage ≅
      F.sheafPushforwardContinuous (Type (u + 1)) J K := by
    simpa [bigSmoothMorphismOfTopoi, F, J, K] using
      (F.sheafPullbackCocontinuousIsoSheafPushforwardContinuous (Type (u + 1)) J K)
  exact preservesLimitsOfShape_of_natIso
    (Adjunction.leftAdjointUniq
      ((F.sheafAdjunctionContinuous (Type (u + 1)) J K).ofNatIsoRight i.symm)
      (Adjunction.ofIsRightAdjoint (bigSmoothMorphismOfTopoi B f).inverseImage))

/-- The lower shriek of a big smooth morphism of topoi preserves fibre products. -/
@[stacks 04HC "shriek_limits"]
public noncomputable instance bigSmoothLowerShriek_preservesPullbacks
    (B : BigSmoothSite.{u}) {T S : B.category} (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingCospan
      (bigSmoothMorphismOfTopoi B f).inverseImage.leftAdjoint :=
  bigSmoothLowerShriekShape B f

/-- The lower shriek of a big smooth morphism of topoi preserves equalizers. -/
@[stacks 04HC "shriek_limits"]
public noncomputable instance bigSmoothLowerShriek_preservesEqualizers
    (B : BigSmoothSite.{u}) {T S : B.category} (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingParallelPair
      (bigSmoothMorphismOfTopoi B f).inverseImage.leftAdjoint := by
  have := bigSmoothOver_hasEqualizers B T
  have := bigSmoothOver_hasEqualizers B S
  exact bigSmoothLowerShriekShape B f

end AlgebraicGeometry
