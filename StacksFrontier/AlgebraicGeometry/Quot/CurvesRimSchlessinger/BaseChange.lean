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
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesRimSchlessinger.BoundedProperCore
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesRimSchlessinger.ProperFibres
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesRimSchlessinger.BoundedProperCore

/-!
# Restriction of curves along a base morphism from Stacks 0D1J

A base-change functor for `Spaces'_{fp, flat, proper}` preserves relative dimension at most one
and so restricts to the bounded cores; transported along the fibre equivalence, it gives a
`AlgebraicGeometry.CurveBaseChange` for families of curves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

private theorem pointsMap_id_local {S : Scheme.{u}} (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} :
    Space.pointsMap B S hS F (𝟙 F) = id := by
  funext x
  induction x using Quot.inductionOn with
  | _ p => rfl

private theorem pointsMap_comp_local {S : Scheme.{u}} (hS : B.Contains S)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (g : G ⟶ H) :
    Space.pointsMap B S hS F (f ≫ g) =
      Space.pointsMap B S hS G g ∘ Space.pointsMap B S hS F f := by
  funext x
  induction x using Quot.inductionOn with
  | _ p => rfl

private theorem relativeDimensionLE_of_overIso {U : B.Schemes}
    {X Y : Space.FpFlatProperOver B integerBase hZ
      (siteLift B hZ U)} (e : X.obj ≅ Y.obj)
    (hX : Space.HasRelativeDimensionLE 1 B integerBase hZ
      X.obj.hom.hom) :
    Space.HasRelativeDimensionLE 1 B integerBase hZ
      Y.obj.hom.hom := by
  let f := X.obj.hom.hom
  let f' := Y.obj.hom.hom
  let g' := e.inv.left.hom
  have hcomm : g' ≫ f = f' := by
    change e.inv.left.hom ≫ X.obj.hom.hom = Y.obj.hom.hom
    exact congrArg (fun q => q.hom) e.inv.w
  have : IsIso g' := by
    refine ⟨⟨e.hom.left.hom, ?_, ?_⟩⟩
    · change e.inv.left.hom ≫ e.hom.left.hom = _
      exact congrArg (fun q => q.left.hom) e.inv_hom_id
    · change e.hom.left.hom ≫ e.inv.left.hom = _
      exact congrArg (fun q => q.left.hom) e.hom_inv_id
  have hpull : IsPullback g' f' f
      (𝟙 (schemeSpace (siteLift B hZ U)).obj) :=
    IsPullback.of_horiz_isIso (CommSq.mk (by simpa [f, f', g'] using hcomm))
  have hfinite : Space.IsLocallyOfFiniteType B integerBase hZ f :=
    Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation
      B integerBase hZ X.property.1.1
  intro y
  let x : Space.points B integerBase hZ X.obj.left.obj :=
    Space.pointsMap B integerBase hZ Y.obj.left.obj g' y
  obtain ⟨d, hd, hdim⟩ := hX x
  refine ⟨d, hd, ?_⟩
  have hdim' := (Space.hasRelativeDimensionAt_iff_of_isPullback
    B integerBase hZ hpull X.obj.left.property
    (schemeSpace (siteLift B hZ U)).property
    (schemeSpace (siteLift B hZ U)).property hfinite
    y d).mp hdim
  simpa [f', x] using hdim'

private theorem properPushout_relativeDimensionLE_iff
    {T T' S S' : B.Schemes} {i : T ⟶ T'} {f : T ⟶ S}
    {g : T' ⟶ S'} {h : S ⟶ S'}
    (d : Space.ProperPushoutEquivalenceData B integerBase hZ
      (siteLiftMap B hZ i) (siteLiftMap B hZ f)
      (siteLiftMap B hZ g) (siteLiftMap B hZ h))
    (hthick : Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B integerBase hZ).map
        (siteLiftMap B hZ h)))
    (Z : Space.FpFlatProperOver B integerBase hZ
      (siteLift B hZ S')) :
    Space.HasRelativeDimensionLE 1 B integerBase hZ
        Z.obj.hom.hom ↔
      Space.HasRelativeDimensionLE 1 B integerBase hZ
        (d.restrictionFunctor.obj Z).fst.obj.hom.hom := by
  constructor
  · intro hdim
    have hbase := properBaseChange_relativeDimensionLE B hZ
      d.fromPushoutToS Z hdim
    let eOver := (ObjectProperty.ι _).mapIso
      (asIso (d.restriction_toS.inv.app Z))
    exact relativeDimensionLE_of_overIso B hZ eOver hbase
  · intro hdim
    let eOver := (ObjectProperty.ι _).mapIso
      (asIso (d.restriction_toS.hom.app Z))
    have hbase := relativeDimensionLE_of_overIso B hZ eOver hdim
    exact properBaseChange_reflects_relativeDimensionLE_of_thickening B hZ
      hthick d.fromPushoutToS Z hbase

private noncomputable def properBaseChangeOnBounded
    {U V : B.Schemes} (f : U ⟶ V)
    (bc : Space.ProperPushoutBaseChange B integerBase hZ
      (siteLiftMap B hZ f)) : BoundedProperCore B hZ V ⥤
        BoundedProperCore B hZ U where
  obj Z := ⟨⟨bc.functor.obj Z.1.1⟩,
    properBaseChange_relativeDimensionLE B hZ bc Z.1.1 Z.2⟩
  map α := by
    letI : IsIso α.1.1 :=
      (MorphismProperty.isomorphisms.iff α.1.1).mp α.1.2
    refine ObjectProperty.homMk ?_
    refine ⟨bc.functor.map α.1.1, ?_⟩
    exact MorphismProperty.isomorphisms.infer_property _
  map_id Z := by
    apply ObjectProperty.hom_ext
    apply WideSubcategory.hom_ext
    simp
  map_comp α β := by
    apply ObjectProperty.hom_ext
    apply WideSubcategory.hom_ext
    simp

private noncomputable def curveFiberEquivalence (U : B.Schemes) :
    (curvesProjection B hZ).Fiber U ≌
      BoundedProperCore B hZ U := by
  let F := curveFiberToBoundedProperCore B hZ U
  letI : F.IsEquivalence := curveFiberToBoundedProperCore_isEquivalence B hZ U
  exact F.asEquivalence

private noncomputable def curveBaseChangeFunctorOfProper
    {U V : B.Schemes} (f : U ⟶ V)
    (bc : Space.ProperPushoutBaseChange B integerBase hZ
      (siteLiftMap B hZ f)) :
    (curvesProjection B hZ).Fiber V ⥤
      (curvesProjection B hZ).Fiber U :=
  (curveFiberEquivalence B hZ V).functor ⋙
    properBaseChangeOnBounded B hZ f bc ⋙
    (curveFiberEquivalence B hZ U).inverse

private noncomputable def curveBaseChange_transportIso
    {U V : B.Schemes} (f : U ⟶ V)
    (bc : Space.ProperPushoutBaseChange B integerBase hZ
      (siteLiftMap B hZ f)) :
    curveBaseChangeFunctorOfProper B hZ f bc ⋙
        (curveFiberEquivalence B hZ U).functor ≅
      (curveFiberEquivalence B hZ V).functor ⋙
        properBaseChangeOnBounded B hZ f bc := by
  let E := curveFiberEquivalence B hZ U
  let F := (curveFiberEquivalence B hZ V).functor ⋙
    properBaseChangeOnBounded B hZ f bc
  change (F ⋙ E.inverse) ⋙ E.functor ≅ F
  exact Functor.associator F E.inverse E.functor ≪≫
    isoWhiskerLeft F E.counitIso ≪≫ Functor.rightUnitor F

private noncomputable def boundedCoreToOver (U : B.Schemes) :
    BoundedProperCore B hZ U ⥤
      Over (schemeSpace (siteLift B hZ U)) :=
  ObjectProperty.ι _ ⋙ wideSubcategoryInclusion _ ⋙
    ObjectProperty.ι _

private noncomputable def boundedCoreIsoToOver {U : B.Schemes}
    {X Y : BoundedProperCore B hZ U} (e : X ≅ Y) :
    (boundedCoreToOver B hZ U).obj X ≅
      (boundedCoreToOver B hZ U).obj Y :=
  (boundedCoreToOver B hZ U).mapIso e

private theorem curveFiberAsProperOver_iso_naturality (U : B.Schemes)
    {Z Z' : (curvesProjection B hZ).Fiber U} (α : Z ⟶ Z') :
    (boundedCoreToOver B hZ U).map
        ((curveFiberToBoundedProperCore B hZ U).map α) ≫
      (curveFiberAsProperOver_iso B hZ Z').hom =
    (curveFiberAsProperOver_iso B hZ Z).hom ≫
      (curveObjectAsOverFunctor B hZ U).map α := by
  apply Over.OverMorphism.ext
  simp [boundedCoreToOver,
    curveFiberToBoundedProperCore, curveFiberToBoundedProperCoreMap,
    curveObjectAsOverFunctor, Category.assoc]


/-- The isomorphism between the base-changed object and the curve family `f^* Z` over `U`. -/
private noncomputable def curveBaseChangeOverIso
    {U V : B.Schemes} (f : U ⟶ V)
    (bc : Space.ProperPushoutBaseChange B integerBase hZ
      (siteLiftMap B hZ f))
    (Z : (curvesProjection B hZ).Fiber V) :
    (bc.functor.obj (curveFiberAsProperOver B hZ Z)).obj ≅
      curveObjectAsOver B hZ ((curveBaseChangeFunctorOfProper B hZ f bc).obj Z) :=
  (boundedCoreIsoToOver (B := B) (hZ := hZ)
      ((curveBaseChange_transportIso B hZ f bc).app Z)).symm ≪≫
    curveFiberAsProperOver_iso B hZ ((curveBaseChangeFunctorOfProper B hZ f bc).obj Z)

private noncomputable def curveBaseChangeComparisonHomOfProper
    {U V : B.Schemes} (f : U ⟶ V)
    (bc : Space.ProperPushoutBaseChange B integerBase hZ
      (siteLiftMap B hZ f))
    (Z : (curvesProjection B hZ).Fiber V) :
    CurveFamily.Hom B hZ
      ((curveBaseChangeFunctorOfProper B hZ f bc).obj Z).1 Z.1 := by
  let Y := (curveBaseChangeFunctorOfProper B hZ f bc).obj Z
  let Pobj := curveFiberAsProperOver B hZ Z
  let eBover := curveFiberAsProperOver_iso B hZ Z
  let eAover := curveBaseChangeOverIso B hZ f bc Z
  let eAalg := (Over.forget _).mapIso eAover
  let eBalg := (Over.forget _).mapIso eBover
  let cmp := bc.comparison.app Pobj
  let eYU := fiberBaseIso B hZ Y
  let eZV := fiberBaseIso B hZ Z
  let baseMap := eYU.hom ≫ siteLiftMap B hZ f ≫ eZV.inv
  refine ⟨baseMap,
    (eAalg.inv ≫ cmp ≫ eBalg.hom), ?_⟩
  exact (bc.cartesian Pobj).of_iso eAalg eBalg
    (schemeSpaceMapIso B hZ eYU.symm)
    (schemeSpaceMapIso B hZ eZV.symm)
    (by
      calc
        cmp ≫ eBalg.hom = 𝟙 _ ≫ cmp ≫ eBalg.hom := by simp
        _ = eAalg.hom ≫ eAalg.inv ≫ cmp ≫ eBalg.hom :=
          (congrArg (fun k => k ≫ cmp ≫ eBalg.hom) eAalg.hom_inv_id).symm)
    (by
      change (bc.functor.obj Pobj).obj.hom ≫
          schemeSpaceMap eYU.inv =
        eAover.hom.left ≫ Y.1.toBase
      have h := congrArg (fun k => k ≫ (schemeSpaceMapIso B hZ eYU.symm).hom)
        eAover.hom.w
      simpa [eAalg, eAover, eYU, schemeSpaceMapIso, curveObjectAsOver,
        schemeSpaceMap_comp_local, schemeSpaceMap_id_local, Category.assoc] using h.symm)
    (by
      change Pobj.obj.hom ≫ schemeSpaceMap eZV.inv =
        eBover.hom.left ≫ Z.1.toBase
      have h := congrArg (fun k => k ≫ (schemeSpaceMapIso B hZ eZV.symm).hom)
        eBover.hom.w
      simpa [eBalg, eBover, eZV, schemeSpaceMapIso, curveObjectAsOver,
        schemeSpaceMap_comp_local, schemeSpaceMap_id_local, Category.assoc] using h.symm)
    (by
      change schemeSpaceMap (siteLiftMap B hZ f) ≫
          schemeSpaceMap eZV.inv =
        schemeSpaceMap eYU.inv ≫
          schemeSpaceMap baseMap
      rw [← schemeSpaceMap_comp_local, ← schemeSpaceMap_comp_local]
      have hbase : siteLiftMap B hZ f ≫ eZV.inv = eYU.inv ≫ baseMap := by
        dsimp [baseMap]
        simp
      exact congrArg (schemeSpaceMap) hbase)

private noncomputable def curvesBaseChangeOfProper
    {U V : B.Schemes} (f : U ⟶ V)
    (bc : Space.ProperPushoutBaseChange B integerBase hZ
      (siteLiftMap B hZ f)) : CurveBaseChange B hZ f where
  functor := curveBaseChangeFunctorOfProper B hZ f bc
  comparison := {
    app := fun Z => curveBaseChangeComparisonHomOfProper B hZ f bc Z
    naturality := by
      intro Z Z' α
      let β := (curveBaseChangeFunctorOfProper B hZ f bc).map α
      let E_V := curveFiberEquivalence B hZ V
      let E_U := curveFiberEquivalence B hZ U
      let γ := E_V.functor.map α
      let γP := γ.1.1
      have hT := (curveBaseChange_transportIso B hZ f bc).hom.naturality α
      have hTOver := congrArg (fun k => (boundedCoreToOver B hZ U).map k) hT
      have hφ := curveFiberAsProperOver_iso_naturality B hZ V α
      have hψ := curveFiberAsProperOver_iso_naturality B hZ U β
      have hcmp := bc.comparison.naturality γP
      apply CurveFamily.Hom.ext
      · have hβ := fiberBaseIso_naturality B hZ β
        have hα := fiberBaseIso_naturality B hZ α
        change β.1.baseMap ≫
            ((fiberBaseIso B hZ
              ((curveBaseChangeFunctorOfProper B hZ f bc).obj Z')).hom ≫
              siteLiftMap B hZ f ≫ (fiberBaseIso B hZ Z').inv) =
          ((fiberBaseIso B hZ
            ((curveBaseChangeFunctorOfProper B hZ f bc).obj Z)).hom ≫
            siteLiftMap B hZ f ≫ (fiberBaseIso B hZ Z).inv) ≫ α.1.baseMap
        have hz : (fiberBaseIso B hZ Z).inv ≫ α.1.baseMap =
            (fiberBaseIso B hZ Z').inv := by
          apply (cancel_mono (fiberBaseIso B hZ Z').hom).1
          calc
            ((fiberBaseIso B hZ Z).inv ≫ α.1.baseMap) ≫
                (fiberBaseIso B hZ Z').hom =
              (fiberBaseIso B hZ Z).inv ≫ (fiberBaseIso B hZ Z).hom := by
                rw [Category.assoc, hα]
            _ = (fiberBaseIso B hZ Z').inv ≫
                (fiberBaseIso B hZ Z').hom := by simp
        calc
          β.1.baseMap ≫
              ((fiberBaseIso B hZ
                ((curveBaseChangeFunctorOfProper B hZ f bc).obj Z')).hom ≫
                siteLiftMap B hZ f ≫
                (fiberBaseIso B hZ Z').inv) =
            (fiberBaseIso B hZ
              ((curveBaseChangeFunctorOfProper B hZ f bc).obj Z)).hom ≫
              siteLiftMap B hZ f ≫
              (fiberBaseIso B hZ Z').inv := by
                rw [← Category.assoc, hβ]
          _ = ((fiberBaseIso B hZ
              ((curveBaseChangeFunctorOfProper B hZ f bc).obj Z)).hom ≫
              siteLiftMap B hZ f ≫ (fiberBaseIso B hZ Z).inv) ≫ α.1.baseMap := by
                rw [← hz]
                simp only [Category.assoc]
      · dsimp [curveBaseChangeComparisonHomOfProper]
        have hφ' := congrArg Over.Hom.left hφ
        let bY := curveFiberAsProperOver_iso B hZ
          ((curveBaseChangeFunctorOfProper B hZ f bc).obj Z)
        let bY' := curveFiberAsProperOver_iso B hZ
          ((curveBaseChangeFunctorOfProper B hZ f bc).obj Z')
        let kβ := (boundedCoreToOver B hZ U).map
          ((curveFiberToBoundedProperCore B hZ U).map β)
        let cβ : curveObjectAsOver B hZ
            ((curveBaseChangeFunctorOfProper B hZ f bc).obj Z) ⟶
            curveObjectAsOver B hZ
              ((curveBaseChangeFunctorOfProper B hZ f bc).obj Z') :=
          (curveObjectAsOverFunctor B hZ U).map β
        have hψOver : kβ ≫ bY'.hom = bY.hom ≫ cβ := hψ
        have hψInvOver : cβ ≫ bY'.inv = bY.inv ≫ kβ := by
          apply (cancel_mono bY'.hom).1
          calc
            (cβ ≫ bY'.inv) ≫ bY'.hom = cβ := by simp
            _ = bY.inv ≫ (bY.hom ≫ cβ) := by simp
            _ = bY.inv ≫ (kβ ≫ bY'.hom) :=
                congrArg (fun k => bY.inv ≫ k) hψOver.symm
            _ = (bY.inv ≫ kβ) ≫ bY'.hom := (Category.assoc _ _ _).symm
        let Y := (curveBaseChangeFunctorOfProper B hZ f bc).obj Z
        let Y' := (curveBaseChangeFunctorOfProper B hZ f bc).obj Z'
        let F := properBaseChangeOnBounded B hZ f bc
        let P := E_V.functor.obj Z
        let P' := E_V.functor.obj Z'
        let Q := F.obj P
        let Q' := F.obj P'
        let eT := (curveBaseChange_transportIso B hZ f bc).app Z
        let eT' := (curveBaseChange_transportIso B hZ f bc).app Z'
        have hcoreY : (boundedCoreToOver B hZ U).obj (E_U.functor.obj Y) =
            (curveFiberAsProperOver B hZ Y).obj := by
          rfl
        have hcoreY' : (boundedCoreToOver B hZ U).obj (E_U.functor.obj Y') =
            (curveFiberAsProperOver B hZ Y').obj := by
          rfl
        let eA : Q.1.1.obj ≅ curveObjectAsOver B hZ Y :=
          (boundedCoreIsoToOver (B := B) (hZ := hZ) eT).symm ≪≫
            (eqToIso hcoreY ≪≫ bY)
        let Pobj : Space.FpFlatProperOver B integerBase hZ
            (siteLift B hZ V) := curveFiberAsProperOver B hZ Z
        let Pobj' : Space.FpFlatProperOver B integerBase hZ
            (siteLift B hZ V) := curveFiberAsProperOver B hZ Z'
        have hqobj' : Q'.1.1.obj = (bc.functor.obj Pobj').obj := by
          rfl
        let eA' : (bc.functor.obj Pobj').obj ≅ curveObjectAsOver B hZ Y' :=
          eqToIso hqobj'.symm ≪≫
            ((boundedCoreIsoToOver (B := B) (hZ := hZ) eT').symm ≪≫
              (eqToIso hcoreY' ≪≫ bY'))
        let eB := curveFiberAsProperOver_iso B hZ Z
        let eB' := curveFiberAsProperOver_iso B hZ Z'
        let eAalg := (Over.forget _).mapIso eA
        let eAalg' := (Over.forget _).mapIso eA'
        let eBalg := (Over.forget _).mapIso eB
        let eBalg' := (Over.forget _).mapIso eB'
        let cmp := bc.comparison.app Pobj
        let cmp' := bc.comparison.app Pobj'
        let pαOver := (boundedCoreToOver B hZ U).map
          ((properBaseChangeOnBounded B hZ f bc).map (E_V.functor.map α))
        have hTboundedOver :
            (boundedCoreToOver B hZ U).map ((E_U.functor).map β) ≫
              (boundedCoreToOver B hZ U).map eT'.hom =
            (boundedCoreToOver B hZ U).map eT.hom ≫ pαOver := hTOver
        have hTMap := congrArg Over.Hom.left hTboundedOver
        change Over.Hom.left ((boundedCoreToOver B hZ U).map ((E_U.functor).map β)) ≫
            Over.Hom.left ((boundedCoreToOver B hZ U).map eT'.hom) =
          Over.Hom.left ((boundedCoreToOver B hZ U).map eT.hom) ≫
            Over.Hom.left pαOver at hTMap
        have hAcomp :
            (curveObjectAsOverFunctor B hZ U).map β ≫ eA'.inv =
              eA.inv ≫ pαOver := by
          have hcoreYMap : Over.Hom.left ((eqToIso hcoreY).inv) = 𝟙 _ := by
            cases hcoreY
            rfl
          have hcoreY'Map : Over.Hom.left ((eqToIso hcoreY').inv) = 𝟙 _ := by
            cases hcoreY'
            rfl
          have hqobjMap : Over.Hom.left ((eqToIso hqobj'.symm).inv) = 𝟙 _ := by
            cases hqobj'
            rfl
          apply Over.OverMorphism.ext
          change (Over.Hom.left cβ ≫ Over.Hom.left bY'.inv ≫
                Over.Hom.left ((eqToIso hcoreY').inv) ≫
                Over.Hom.left ((boundedCoreToOver B hZ U).mapIso eT').hom ≫
                Over.Hom.left ((eqToIso hqobj'.symm).inv)) =
              (Over.Hom.left bY.inv ≫ Over.Hom.left ((eqToIso hcoreY).inv) ≫
                Over.Hom.left ((boundedCoreToOver B hZ U).mapIso eT).hom) ≫
                Over.Hom.left pαOver
          simp only [hcoreYMap, hcoreY'Map, hqobjMap, Category.assoc]
          have hψinv' : Over.Hom.left cβ ≫ Over.Hom.left bY'.inv =
              Over.Hom.left bY.inv ≫ Over.Hom.left kβ :=
            congrArg Over.Hom.left hψInvOver
          have hTMap' : Over.Hom.left kβ ≫
                Over.Hom.left ((boundedCoreToOver B hZ U).mapIso eT').hom =
              Over.Hom.left ((boundedCoreToOver B hZ U).mapIso eT).hom ≫
                Over.Hom.left pαOver := hTMap
          calc
            _ = (Over.Hom.left cβ ≫ Over.Hom.left bY'.inv) ≫
                Over.Hom.left ((boundedCoreToOver B hZ U).mapIso eT').hom := by
                  cat_disch
            _ = (Over.Hom.left bY.inv ≫ Over.Hom.left kβ) ≫
                Over.Hom.left ((boundedCoreToOver B hZ U).mapIso eT').hom :=
                  congrArg (fun k => k ≫
                    Over.Hom.left ((boundedCoreToOver B hZ U).mapIso eT').hom) hψinv'
            _ = Over.Hom.left bY.inv ≫
                (Over.Hom.left kβ ≫
                  Over.Hom.left ((boundedCoreToOver B hZ U).mapIso eT').hom) := by
                  cat_disch
            _ = Over.Hom.left bY.inv ≫
                (Over.Hom.left ((boundedCoreToOver B hZ U).mapIso eT).hom ≫
                  Over.Hom.left pαOver) :=
                  congrArg (fun k => Over.Hom.left bY.inv ≫ k) hTMap'
            _ = _ := by cat_disch
        change β.1.totalMap ≫ (eAalg'.inv ≫ cmp' ≫ eBalg'.hom) =
          (eAalg.inv ≫ cmp ≫ eBalg.hom) ≫ α.1.totalMap
        let cα := (boundedCoreToOver B hZ V).map (E_V.functor.map α)
        have hAcompMap := congrArg Over.Hom.left hAcomp
        change β.1.totalMap ≫ eAalg'.inv =
          eAalg.inv ≫ Over.Hom.left pαOver at hAcompMap
        change Over.Hom.left pαOver ≫ cmp' =
          cmp ≫ Over.Hom.left cα at hcmp
        change Over.Hom.left cα ≫ Over.Hom.left eB'.hom =
          Over.Hom.left eB.hom ≫ α.1.totalMap at hφ'
        have hφMap' : Over.Hom.left cα ≫ eBalg'.hom =
            eBalg.hom ≫ α.1.totalMap := by
          simpa [eBalg, eBalg'] using hφ'
        have step : β.1.totalMap ≫ eAalg'.inv ≫ cmp' ≫ eBalg'.hom =
            eAalg.inv ≫ cmp ≫ eBalg.hom ≫ α.1.totalMap :=
          ((Category.assoc _ _ _).symm.trans
              (congrArg (fun k => k ≫ cmp' ≫ eBalg'.hom) hAcompMap)).trans
            (((Category.assoc _ _ _).trans
                (congrArg (fun k => eAalg.inv ≫ k)
                  (Category.assoc _ _ _).symm)).trans
              ((congrArg (fun k => eAalg.inv ≫ k ≫ eBalg'.hom) hcmp).trans
                ((congrArg (fun k => eAalg.inv ≫ k) (Category.assoc _ _ _)).trans
                  (congrArg (fun k => eAalg.inv ≫ cmp ≫ k) hφMap'))))
        exact step.trans (Category.assoc _ _ _).symm }
  comparison_base := by
    intro Z
    let Y := (curveBaseChangeFunctorOfProper B hZ f bc).obj Z
    let H := curveBaseChangeComparisonHomOfProper B hZ f bc Z
    refine IsHomLift.of_fac (p := curvesProjection B hZ)
      f H Y.2 Z.2 ?_
    change f = (fiberBaseIso B hZ Y).inv.left ≫
      (fiberBaseIso B hZ Y).hom.left ≫ (siteLiftMap B hZ f).left ≫
      (fiberBaseIso B hZ Z).inv.left ≫ (fiberBaseIso B hZ Z).hom.left
    simp only [Over.inv_left_hom_left_assoc, Over.inv_left_hom_left, Category.comp_id]
    rfl

end AlgebraicGeometry

end
