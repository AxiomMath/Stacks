module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.Widesubcategory
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushout07RT
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGlobal
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
import Mathlib.AlgebraicGeometry.PullbackCarrier
import StacksFrontier.AlgebraicGeometry.Spaces.Category
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
import StacksFrontier.AlgebraicGeometry.Spaces.Points
import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedFunctor
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesRimSchlessinger.ProperFibres
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesRimSchlessinger.ProperFibres

/-!
# The fibre of curves as a bounded core of proper spaces

The scheme site is closed under isomorphisms and pullbacks, base change of `Spaces'_{fp, flat,
proper}` along a thickening is surjective on points and reflects relative dimension at most one,
and the fibre category of curves over `U` is equivalent to the core of finitely presented, flat
and proper algebraic spaces over `U` of relative dimension at most one. This part also defines
`AlgebraicGeometry.CurveBaseChange` and `AlgebraicGeometry.CurvePushoutEquivalenceData`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

private theorem schemeSite_closedUnderIsomorphisms :
    (schemeSizeBelow B.cutoff).IsClosedUnderIsomorphisms := ⟨by
  intro X Y e hX
  change Y.size < B.cutoff
  rw [← Scheme.size_congr e]
  exact hX⟩

attribute [local instance] schemeSite_closedUnderIsomorphisms

private theorem schemeSite_closedUnderPullbacks :
    (schemeSizeBelow B.cutoff).IsClosedUnderLimitsOfShape WalkingCospan := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  change (limit F).size < B.cutoff
  rw [Scheme.size_congr (HasLimit.isoOfNatIso (diagramIsoCospan F))]
  exact Scheme.size_pullback_lt _ _ (hF .left) (hF .right)

attribute [local instance] schemeSite_closedUnderPullbacks

private theorem preservesPullbacks_siteToScheme :
    PreservesLimitsOfShape WalkingCospan
      (BigFppfOver.toScheme B integerBase hZ) := by
  apply comp_preservesLimitsOfShape

attribute [local instance] preservesPullbacks_siteToScheme

private theorem pointsMap_surjective_of_properBaseChange_thickening
    {U V : BigFppfOver B integerBase hZ} {f : U ⟶ V}
    (hf : Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B integerBase hZ).map f))
    (bc : Space.ProperPushoutBaseChange B integerBase hZ f)
    (Z : Space.FpFlatProperOver B integerBase hZ V) :
    Function.Surjective (fun x => Space.pointsMap B integerBase hZ
      (bc.functor.obj Z).obj.left.obj (bc.comparison.app Z).hom x) := by
  let T := BigFppfOver.toScheme B integerBase hZ
  let P : MorphismProperty (BigFppfOver B integerBase hZ) :=
    MorphismProperty.inverseImage (@Surjective) T
  let : HasPullbacks (BigFppfOver B integerBase hZ) := inferInstance
  let : P.IsStableUnderBaseChange := ⟨by
    intro X Y Y' Z' a b a' b' hsq hb
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Surjective) (hsq.map T) hb⟩
  let : P.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange P
  have hbase : P f := by
    change Surjective (T.map f)
    exact ⟨hf.2⟩
  have hbase' : P.presheaf (yoneda.map f) :=
    MorphismProperty.relative_map (P := P) (F := yoneda) hbase
  let f' := Z.obj.hom.hom
  let g' := schemeSpaceMap f
  let fp := AlgebraicSpaces.fiberProduct B integerBase hZ
    Z.obj.hom (schemeSpaceMap f)
  have hfp := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ
    Z.obj.hom (schemeSpaceMap f)
  let hout := bc.cartesian Z
  let eAlg := hout.isoIsPullback _ _ hfp
  let e := (ObjectProperty.ι _).mapIso eAlg
  have hsq' : IsPullback (bc.comparison.app Z).hom
      (bc.functor.obj Z).obj.hom.hom f' g'.hom := by
    refine (IsPullback.of_hasPullback f' g'.hom).of_iso e.symm (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (congrArg (fun q => q.hom)
        (IsPullback.isoIsPullback_inv_fst _ _ hout hfp)).symm
    · exact (congrArg (fun q => q.hom)
        (IsPullback.isoIsPullback_inv_snd _ _ hout hfp)).symm
    · simp [f']
    · simp [g']
  have hc : P.presheaf (bc.comparison.app Z).hom :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq'.flip hbase'
  exact (Space.presheafSurjective_iff_isSurjective
    B integerBase hZ (bc.functor.obj Z).obj.left.property
    Z.obj.left.property (bc.comparison.app Z).hom hc.rep).mp hc

private theorem properBaseChange_reflects_relativeDimensionLE_of_thickening
    {U V : BigFppfOver B integerBase hZ} {f : U ⟶ V}
    (hf : Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B integerBase hZ).map f))
    (bc : Space.ProperPushoutBaseChange B integerBase hZ f)
    (Z : Space.FpFlatProperOver B integerBase hZ V)
    (hDim : Space.HasRelativeDimensionLE 1 B integerBase hZ
      (bc.functor.obj Z).obj.hom.hom) :
    Space.HasRelativeDimensionLE 1 B integerBase hZ Z.obj.hom.hom :=
  properBaseChange_reflects_relativeDimensionLE B hZ bc Z hDim
    (pointsMap_surjective_of_properBaseChange_thickening B hZ hf bc Z)

private noncomputable def curveFiberAsProperOver_iso {U : B.Schemes}
    (Z : (curvesProjection B hZ).Fiber U) :
    (curveFiberAsProperOver B hZ Z).obj ≅ curveObjectAsOver B hZ Z := Iso.refl _

private abbrev ProperCore (U : B.Schemes) :=
  WideSubcategory (MorphismProperty.isomorphisms
    (Space.FpFlatProperOver B integerBase hZ (siteLift B hZ U)))

private abbrev BoundedProperCore (U : B.Schemes) :=
  (show ObjectProperty (ProperCore B hZ U) from fun X =>
    Space.HasRelativeDimensionLE 1 B integerBase hZ
      X.1.obj.hom.hom).FullSubcategory

private noncomputable def curveFiberToBoundedProperCoreMap (U : B.Schemes)
    {Z Z' : (curvesProjection B hZ).Fiber U} (α : Z ⟶ Z') :
    (⟨⟨curveFiberAsProperOver B hZ Z⟩,
      curveFiberAsProperOver_relativeDimensionLE B hZ Z⟩ :
        BoundedProperCore B hZ U) ⟶
    (⟨⟨curveFiberAsProperOver B hZ Z'⟩,
      curveFiberAsProperOver_relativeDimensionLE B hZ Z'⟩ :
        BoundedProperCore B hZ U) := by
  let e := curveFiberAsProperOver_iso B hZ Z
  let e' := curveFiberAsProperOver_iso B hZ Z'
  letI : IsGroupoid ((curvesProjection B hZ).Fiber U) :=
    (curvesProjection_isFiberedInGroupoids B hZ).fiber_isGroupoid U
  let aIso : curveObjectAsOver B hZ Z ≅ curveObjectAsOver B hZ Z' :=
    (curveObjectAsOverFunctor B hZ U).mapIso (asIso α)
  let mIso := e ≪≫ aIso ≪≫ e'.symm
  let mSub : curveFiberAsProperOver B hZ Z ⟶ curveFiberAsProperOver B hZ Z' :=
    ObjectProperty.homMk mIso.hom
  let mSubInv : curveFiberAsProperOver B hZ Z' ⟶ curveFiberAsProperOver B hZ Z :=
    ObjectProperty.homMk mIso.inv
  let subIso : curveFiberAsProperOver B hZ Z ≅ curveFiberAsProperOver B hZ Z' :=
    { hom := mSub
      inv := mSubInv
      hom_inv_id := ObjectProperty.hom_ext _ mIso.hom_inv_id
      inv_hom_id := ObjectProperty.hom_ext _ mIso.inv_hom_id }
  letI : IsIso mSub := subIso.isIso_hom
  exact ObjectProperty.homMk ⟨mSub, inferInstance⟩

/-- The underlying morphism of `curveFiberToBoundedProperCoreMap α` is the image of `α`. -/
private theorem curveFiberToBoundedProperCoreMap_hom (U : B.Schemes)
    {Z Z' : (curvesProjection B hZ).Fiber U} (α : Z ⟶ Z') :
    (curveFiberToBoundedProperCoreMap B hZ U α).hom.hom.hom =
      (curveObjectAsOverFunctor B hZ U).map α := by
  let : IsGroupoid ((curvesProjection B hZ).Fiber U) :=
    (curvesProjection_isFiberedInGroupoids B hZ).fiber_isGroupoid U
  simp [curveFiberToBoundedProperCoreMap, curveFiberAsProperOver_iso]
  rfl

private noncomputable def curveFiberToBoundedProperCore (U : B.Schemes) :
    (curvesProjection B hZ).Fiber U ⥤ BoundedProperCore B hZ U where
  obj Z := ⟨⟨curveFiberAsProperOver B hZ Z⟩,
    curveFiberAsProperOver_relativeDimensionLE B hZ Z⟩
  map := fun {Z Z'} α => curveFiberToBoundedProperCoreMap B hZ U α
  map_id Z := by
    apply ObjectProperty.hom_ext
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    rw [curveFiberToBoundedProperCoreMap_hom]
    exact (curveObjectAsOverFunctor B hZ U).map_id Z
  map_comp := by
    intro Z₁ Z₂ Z₃ α β
    apply ObjectProperty.hom_ext
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    change (curveFiberToBoundedProperCoreMap B hZ U (α ≫ β)).hom.hom.hom =
      (curveFiberToBoundedProperCoreMap B hZ U α).hom.hom.hom ≫
        (curveFiberToBoundedProperCoreMap B hZ U β).hom.hom.hom
    simp only [curveFiberToBoundedProperCoreMap_hom]
    exact (curveObjectAsOverFunctor B hZ U).map_comp α β

private theorem curveFiberToBoundedProperCore_faithful (U : B.Schemes) :
    (curveFiberToBoundedProperCore B hZ U).Faithful where
  map_injective := by
    intro Z Z' α β hab
    have hmap := congrArg (fun m => m.hom.hom.hom) hab
    simp only [curveFiberToBoundedProperCore, curveFiberToBoundedProperCoreMap_hom] at hmap
    have hcore : (curveObjectAsOverCoreFunctor B hZ U).map α =
        (curveObjectAsOverCoreFunctor B hZ U).map β :=
      WideSubcategory.hom_ext _ hmap
    exact (curveObjectAsOverCoreFunctor_faithful B hZ U).map_injective hcore

private theorem curveFiberToBoundedProperCore_full (U : B.Schemes) :
    (curveFiberToBoundedProperCore B hZ U).Full where
  map_surjective := by
    intro Z Z' α
    let e := curveFiberAsProperOver_iso B hZ Z
    let e' := curveFiberAsProperOver_iso B hZ Z'
    let : IsIso α.1.1 := (MorphismProperty.isomorphisms.iff α.1.1).mp α.1.2
    let αover : (curveFiberAsProperOver B hZ Z).obj ⟶
        (curveFiberAsProperOver B hZ Z').obj :=
      (ObjectProperty.ι _).map α.1.1
    let : IsIso αover := Functor.map_isIso (ObjectProperty.ι _) α.1.1
    let mIso := e.symm ≪≫ asIso αover ≪≫ e'
    let m := mIso.hom
    let : IsIso m := mIso.isIso_hom
    let αcore :
        (curveObjectAsOverCoreFunctor B hZ U).obj Z ⟶
          (curveObjectAsOverCoreFunctor B hZ U).obj Z' :=
      ⟨m, MorphismProperty.isomorphisms.infer_property m⟩
    obtain ⟨β, hβ⟩ :=
      (curveObjectAsOverCoreFunctor_full B hZ U).map_surjective αcore
    refine ⟨β, ?_⟩
    apply ObjectProperty.hom_ext
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    change e.hom ≫ ((curveObjectAsOverFunctor B hZ U).map β) ≫ e'.inv =
      αover
    have hβ' := congrArg (fun q => q.hom) hβ
    change (curveObjectAsOverFunctor B hZ U).map β = m at hβ'
    rw [hβ']
    calc
      e.hom ≫ (e.inv ≫ αover ≫ e'.hom) ≫ e'.inv =
          (e.hom ≫ e.inv) ≫ (αover ≫ (e'.hom ≫ e'.inv)) := by cat_disch
      _ = αover := by simp

private theorem pushout_map_isThickening
    {T T' S S' : B.Schemes} (i : T ⟶ T') (f : T ⟶ S)
    (g : T' ⟶ S') (h : S ⟶ S')
    (hi : Stacks.Thickenings.IsThickening (B.inclusion.map i))
    [IsAffineHom (B.inclusion.map f)]
    (hsq : IsPushout (B.inclusion.map i) (B.inclusion.map f)
      (B.inclusion.map g) (B.inclusion.map h)) :
    Stacks.Thickenings.IsThickening (B.inclusion.map h) := by
  let i₀ := B.inclusion.map i
  let f₀ := B.inclusion.map f
  let h₀ := B.inclusion.map h
  let : HasPushout i₀ f₀ :=
    Stacks.Pushout.hasPushout_of_isThickening_of_isAffineHom
      Stacks.Thickenings.forall_isAffine_of_isThickening i₀ f₀ hi
  have h₁ : Stacks.Thickenings.IsThickening (pushout.inr i₀ f₀) :=
    Stacks.Pushout.pushout_inr_isThickening
      Stacks.Thickenings.forall_isAffine_of_isThickening i₀ f₀ hi
  let e := hsq.isoPushout
  have heq : h₀ = pushout.inr i₀ f₀ ≫ e.inv := by
    apply (cancel_mono e.hom).1
    simp [e]
  constructor
  · change IsClosedImmersion h₀
    rw [heq]
    let : IsClosedImmersion (pushout.inr i₀ f₀) := h₁.1
    infer_instance
  · intro s'
    obtain ⟨s, hs⟩ := h₁.2 (e.hom s')
    refine ⟨s, ?_⟩
    change h₀ s = s'
    rw [heq]
    change e.inv (pushout.inr i₀ f₀ s) = s'
    rw [hs]
    simp

/-- Restriction of families of curves along a base morphism, with the natural
cartesian arrow from a restricted family to its original family. -/
structure CurveBaseChange {U V : B.Schemes} (f : U ⟶ V) where
  /-- The restriction functor on fibre categories of curves. -/
  functor : (curvesProjection B hZ).Fiber V ⥤
    (curvesProjection B hZ).Fiber U
  /-- The comparison from a restricted family to the family it came from. -/
  comparison :
    functor ⋙ Functor.Fiber.fiberInclusion ⟶ Functor.Fiber.fiberInclusion
  /-- Each component of the comparison lies over `f`. -/
  comparison_base
      (Z : (curvesProjection B hZ).Fiber V) :
    (curvesProjection B hZ).IsHomLift f
      (comparison.app Z)

/-- The canonical restriction equivalence for curves, including its
base-change functors and all projection and overlap comparisons. -/
structure CurvePushoutEquivalenceData
    {T T' S S' : B.Schemes}
    (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S') where
  /-- Restriction from `S` to the overlap `T`. -/
  toOverlapFromS : CurveBaseChange B hZ f
  /-- Restriction from `T'` to the overlap `T`. -/
  toOverlapFromT' : CurveBaseChange B hZ i
  /-- Restriction from the pushout `S'` to `S`. -/
  fromPushoutToS : CurveBaseChange B hZ h
  /-- Restriction from the pushout `S'` to `T'`. -/
  fromPushoutToT' : CurveBaseChange B hZ g
  /-- The two routes from `S'` to the overlap `T` agree. -/
  overlapComparison :
    fromPushoutToS.functor ⋙ toOverlapFromS.functor ≅
      fromPushoutToT'.functor ⋙ toOverlapFromT'.functor
  /-- The comparison of the two routes to the overlap is compatible with the cartesian
  comparisons. -/
  overlapComparison_canonical
      (Z : (curvesProjection B hZ).Fiber S') :
    Functor.Fiber.fiberInclusion.map (overlapComparison.hom.app Z) ≫
        toOverlapFromT'.comparison.app (fromPushoutToT'.functor.obj Z) ≫
        fromPushoutToT'.comparison.app Z =
      toOverlapFromS.comparison.app (fromPushoutToS.functor.obj Z) ≫
        fromPushoutToS.comparison.app Z
  /-- The restriction functor to compatible pairs. -/
  restrictionFunctor :
    (curvesProjection B hZ).Fiber S' ⥤
      CategoricalPullback toOverlapFromS.functor toOverlapFromT'.functor
  /-- Restriction is an equivalence. -/
  equivalence : restrictionFunctor.IsEquivalence
  /-- The first projection of the restriction functor is restriction to `S`. -/
  restriction_toS :
    restrictionFunctor ⋙ CategoricalPullback.π₁ _ _ ≅
      fromPushoutToS.functor
  /-- The second projection of the restriction functor is restriction to `T'`. -/
  restriction_toT' :
    restrictionFunctor ⋙ CategoricalPullback.π₂ _ _ ≅
      fromPushoutToT'.functor
  /-- The two projections are compatible with the comparison over the overlap. -/
  restriction_overlap
      (Z : (curvesProjection B hZ).Fiber S') :
    toOverlapFromS.functor.map (restriction_toS.hom.app Z) ≫
        overlapComparison.hom.app Z =
      (restrictionFunctor.obj Z).iso.hom ≫
        toOverlapFromT'.functor.map (restriction_toT'.hom.app Z)

private noncomputable def curveFamilyOfProperOver {U : B.Schemes}
    (Z : Space.FpFlatProperOver B integerBase hZ
      (siteLift B hZ U))
    (hDim : Space.HasRelativeDimensionLE 1 B integerBase hZ
      Z.obj.hom.hom) : CurveFamily B hZ :=
  { base := siteLift B hZ U
    total := Z.obj.left
    toBase := Z.obj.hom
    flat := Z.property.2.1
    proper := Z.property.2.2
    finitePresentation := Z.property.1
    relativeDimensionLE := hDim }

private noncomputable def curveFiberOfProperOver {U : B.Schemes}
    (Z : Space.FpFlatProperOver B integerBase hZ
      (siteLift B hZ U))
    (hDim : Space.HasRelativeDimensionLE 1 B integerBase hZ
      Z.obj.hom.hom) : (curvesProjection B hZ).Fiber U :=
  ⟨curveFamilyOfProperOver B hZ Z hDim, rfl⟩

private theorem curveFiberOfProperOver_baseMap {U : B.Schemes}
    (Z : Space.FpFlatProperOver B integerBase hZ
      (siteLift B hZ U))
    (hDim : Space.HasRelativeDimensionLE 1 B integerBase hZ
      Z.obj.hom.hom) :
    (fiberBaseIso B hZ (curveFiberOfProperOver B hZ Z hDim)).hom =
      𝟙 (siteLift B hZ U) := by
  apply Over.OverMorphism.ext
  change (eqToIso (rfl : (siteLift B hZ U).left = U)).hom = _
  simp

private theorem curveFiberOfProperOver_toBase {U : B.Schemes}
    (Z : Space.FpFlatProperOver B integerBase hZ
      (siteLift B hZ U))
    (hDim : Space.HasRelativeDimensionLE 1 B integerBase hZ
      Z.obj.hom.hom) :
    (curveObjectAsOver B hZ (curveFiberOfProperOver B hZ Z hDim)).hom.hom =
      Z.obj.hom.hom := by
  change Z.obj.hom.hom ≫
    (schemeSpaceMap (fiberBaseIso B hZ
      (curveFiberOfProperOver B hZ Z hDim)).hom).hom = _
  rw [curveFiberOfProperOver_baseMap]
  calc
    Z.obj.hom.hom ≫
        (schemeSpaceMap (𝟙 (siteLift B hZ U))).hom =
      Z.obj.hom.hom ≫
        𝟙 (schemeSpace (siteLift B hZ U)).obj :=
        congrArg (fun q : schemeSpace (siteLift B hZ U) ⟶
            schemeSpace (siteLift B hZ U) => Z.obj.hom.hom ≫ q.hom)
          (schemeSpaceMap_id_local (B := B) (hZ := hZ)
            (U := siteLift B hZ U))
    _ = Z.obj.hom.hom := by simp

private noncomputable def curveFiberOfProperOver_asProperOver_iso
    {U : B.Schemes}
    (Z : Space.FpFlatProperOver B integerBase hZ
      (siteLift B hZ U))
    (hDim : Space.HasRelativeDimensionLE 1 B integerBase hZ
      Z.obj.hom.hom) :
    (curveFiberAsProperOver B hZ
      (curveFiberOfProperOver B hZ Z hDim)).obj ≅ Z.obj := by
  let Zc := curveFiberOfProperOver B hZ Z hDim
  let e := curveFiberAsProperOver_iso B hZ Zc
  let e' : curveObjectAsOver B hZ Zc ≅ Z.obj :=
    Over.isoMk (Iso.refl _)
      (ObjectProperty.hom_ext _ (curveFiberOfProperOver_toBase B hZ Z hDim).symm)
  exact e ≪≫ e'

private noncomputable def curveFiberToBoundedProperCore_preimageIso
    (U : B.Schemes)
    (Z : Space.FpFlatProperOver B integerBase hZ
      (siteLift B hZ U))
    (hDim : Space.HasRelativeDimensionLE 1 B integerBase hZ
      Z.obj.hom.hom) :
    (curveFiberToBoundedProperCore B hZ U).obj
      (curveFiberOfProperOver B hZ Z hDim) ≅
    (⟨⟨Z⟩, hDim⟩ : BoundedProperCore B hZ U) := by
  let eOver := curveFiberOfProperOver_asProperOver_iso B hZ Z hDim
  let eProper := ObjectProperty.isoMk _ eOver
  let eCore : (⟨curveFiberAsProperOver B hZ
      (curveFiberOfProperOver B hZ Z hDim)⟩ : ProperCore B hZ U) ≅ ⟨Z⟩ :=
    WideSubcategory.isoMk eProper (by infer_instance) (by infer_instance)
  exact ObjectProperty.isoMk _ eCore

private theorem curveFiberToBoundedProperCore_essSurj (U : B.Schemes) :
    (curveFiberToBoundedProperCore B hZ U).EssSurj := by
  constructor
  intro X
  let Z : Space.FpFlatProperOver B integerBase hZ
      (siteLift B hZ U) := X.1.obj
  let hDim : Space.HasRelativeDimensionLE 1 B integerBase hZ
      Z.obj.hom.hom := X.2
  refine ⟨curveFiberOfProperOver B hZ Z hDim, ?_⟩
  exact ⟨by
    simpa [Z, hDim, BoundedProperCore] using
      curveFiberToBoundedProperCore_preimageIso B hZ U Z hDim⟩

private theorem curveFiberToBoundedProperCore_isEquivalence (U : B.Schemes) :
    (curveFiberToBoundedProperCore B hZ U).IsEquivalence where
  faithful := curveFiberToBoundedProperCore_faithful B hZ U
  full := curveFiberToBoundedProperCore_full B hZ U
  essSurj := curveFiberToBoundedProperCore_essSurj B hZ U

end AlgebraicGeometry

end
