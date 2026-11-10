module

public import StacksFrontier.AlgebraicGeometry.Descent.Germ.OfSchemeHom
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SmoothnessOverNoetherianBase
public import StacksFrontier.AlgebraicGeometry.Quot.CartesianFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesOverSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Artin.Versality.Openness
import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
import StacksFrontier.AlgebraicGeometry.Spaces.Points
import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
import StacksFrontier.AlgebraicGeometry.Spaces.StronglyCartesian
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import all StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SmoothnessOverNoetherianBase
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality.ProperFlatFamilies
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality.ProperFlatFamilies

/-!
# Openness of versality for curves over `Spec ℤ`

The relative dimension bound for morphisms of finitely presented, flat and proper families over
`Spec ℤ`, the full subcategory `ProperFlatCurves` of those families of relative dimension at most
one, the transport of versality in both directions between it and the families of curves, and
openness of versality for curves over `Spec ℤ` from openness of versality for proper flat
families. The part ends with the relocalized Yoneda charts and the schemes over a larger base
viewed as algebraic spaces, used for the comparison over a Noetherian base.
-/

@[expose] public section

attribute [local implicit_reducible] AlgebraicGeometry.curvesProjectionOver

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Deformation.Artin

universe u

namespace CurvesVersality

attribute [local instance] schemeCutoff_isClosedUnderIsomorphisms
attribute [local instance] schemeCutoff_isClosedUnderPullbacks
attribute [local instance] AlgebraicGeometry.BigFppfSite.hasPullbacks_schemes
attribute [local instance high] hasPullback_presheaf_ProperFlatFamilies
attribute [local instance] hasLimits_presheaf_ProperFlatFamilies
  hasPullbacks_presheaf_ProperFlatFamilies

/-- The source of a morphism of finitely presented, flat and proper families has relative
dimension at most one when its target does. -/
theorem properFlat_relativeDimensionLE_of_hom_over
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : CartesianProperFlatSpaces B S hS} (f : X ⟶ Y)
    (hYdim : Space.HasRelativeDimensionLE 1 B S hS Y.obj.obj.hom) :
    Space.HasRelativeDimensionLE 1 B S hS X.obj.obj.hom := by
  have hft : Space.IsLocallyOfFiniteType B S hS Y.obj.obj.hom :=
    AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
      Y.obj.property.1.1
  exact relativeDimensionLE_of_isPullback B S hS
    (g' := f.hom.hom.left.hom) (f' := X.obj.obj.hom) (f := Y.obj.obj.hom)
    (g := yoneda.map f.hom.hom.right)
    (properFlatHom_isPullback_over B S hS f)
    X.obj.obj.left.property Y.obj.obj.left.property
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS X.obj.obj.right)
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Y.obj.obj.right)
    hft hYdim

/-- An object of `Over S` equal to `Spec R` for an Artinian local ring `R` has subsingleton
source. -/
private theorem subsingleton_left_of_eq_mk {S : Scheme.{u}} {R : Type u} [CommRing R]
    [IsLocalRing R] [IsArtinianRing R] {Q : Over S} {h : Spec (CommRingCat.of R) ⟶ S}
    (hQ : Q = Over.mk h) :
    Subsingleton Q.left := by
  subst hQ
  have : IsLocalRing (CommRingCat.of R) := ‹_›
  have : IsArtinianRing (CommRingCat.of R) := ‹_›
  exact subsingleton_spec_of_isArtinianRing (CommRingCat.of R)

/-- An object of `Over S` equal to `Spec R` for a local ring `R` has nonempty source. -/
private theorem nonempty_left_of_eq_mk {S : Scheme.{u}} {R : Type u} [CommRing R]
    [IsLocalRing R] {Q : Over S} {h : Spec (CommRingCat.of R) ⟶ S} (hQ : Q = Over.mk h) :
    Nonempty Q.left := by
  subst hQ
  exact ⟨IsLocalRing.closedPoint R⟩

private abbrev ProperFlatCurves
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :=
  ObjectProperty.FullSubcategory (fun X : CartesianProperFlatSpaces B S hS =>
    Space.HasRelativeDimensionLE 1 B S hS X.obj.obj.hom)

private noncomputable abbrev properFlatCurvesProjection
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    ProperFlatCurves B S hS ⥤ Over S :=
  ObjectProperty.ι _ ⋙ cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion

private theorem isVersalAt_properFlatCurve_of_curve
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : Over S) (x : ProperFlatCurves B S hS)
    (hx : (properFlatCurvesProjection B S hS).obj x = U)
    (u₀ : U.left)
    (hversal : Deformation.Artin.IsVersalAt U
      (properFlatCurvesProjection B S hS) u₀ x hx) :
    Deformation.Artin.IsVersalAt U
      (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)
      u₀ x.1 (by simpa [properFlatCurvesProjection] using hx) := by
  let := Deformation.Artin.residueFieldAlgebra U u₀
  intro A C f hf y z hy hz i hi a ha
  have hyDim : Space.HasRelativeDimensionLE 1 B S hS y.obj.obj.hom :=
    properFlat_relativeDimensionLE_of_hom_over B S hS a x.2
  let q := cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion
  have hybase : Nonempty (q.obj y).left := nonempty_left_of_eq_mk (R := A.carrier) hy
  have hzsub : Subsingleton (q.obj z).left := subsingleton_left_of_eq_mk (R := C.carrier) hz
  have hzDim := properFlat_relativeDimensionLE_of_artinianArrow B S hS i hyDim
    hybase hzsub
  let cy : ProperFlatCurves B S hS := ⟨y, hyDim⟩
  let cz : ProperFlatCurves B S hS := ⟨z, hzDim⟩
  have hy' : (properFlatCurvesProjection B S hS).obj cy =
      Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap (S.presheaf.stalk
          (Deformation.Artin.basePoint U u₀)) A)) ≫
        S.fromSpecStalk (Deformation.Artin.basePoint U u₀)) := by
    simpa [cy, properFlatCurvesProjection] using hy
  have hz' : (properFlatCurvesProjection B S hS).obj cz =
      Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap (S.presheaf.stalk
          (Deformation.Artin.basePoint U u₀)) C)) ≫
        S.fromSpecStalk (Deformation.Artin.basePoint U u₀)) := by
    simpa [cz, properFlatCurvesProjection] using hz
  let i' : cy ⟶ cz := ObjectProperty.homMk (show cy.obj ⟶ cz.obj from i)
  let a' : cy ⟶ x := ObjectProperty.homMk (show cy.obj ⟶ x.obj from a)
  have hi' : eqToHom (congrArg Over.left hy').symm ≫
      ((properFlatCurvesProjection B S hS).map i').left ≫
        eqToHom (congrArg Over.left hz') =
      Spec.map (CommRingCat.ofHom f.hom.toRingHom) := by
    simpa [i', properFlatCurvesProjection] using hi
  have ha' : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫
      eqToHom (congrArg Over.left hy').symm ≫
      ((properFlatCurvesProjection B S hS).map a').left ≫
      eqToHom (congrArg Over.left hx) = U.left.fromSpecResidueField u₀ := by
    simpa [a', properFlatCurvesProjection] using ha
  obtain ⟨b, hb⟩ := hversal A C f hf cy cz hy' hz' i' hi' a' ha'
  refine ⟨b.hom, ?_⟩
  have hb' := congrArg (fun g => g.hom) hb
  simpa [i', a'] using hb'

private theorem isVersalAt_curve_of_properFlatCurve
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : Over S) (x : ProperFlatCurves B S hS)
    (hx : (properFlatCurvesProjection B S hS).obj x = U)
    (u₀ : U.left)
    (hversal : Deformation.Artin.IsVersalAt U
      (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)
      u₀ x.obj (by simpa [properFlatCurvesProjection] using hx)) :
    Deformation.Artin.IsVersalAt U (properFlatCurvesProjection B S hS) u₀ x hx := by
  let := Deformation.Artin.residueFieldAlgebra U u₀
  intro A C f hf y z hy hz i hi a ha
  let q := cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion
  have hy' : q.obj y.obj =
      Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap (S.presheaf.stalk (Deformation.Artin.basePoint U u₀)) A)) ≫
        S.fromSpecStalk (Deformation.Artin.basePoint U u₀)) := by
    simpa [q, properFlatCurvesProjection] using hy
  have hz' : q.obj z.obj =
      Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap (S.presheaf.stalk (Deformation.Artin.basePoint U u₀)) C)) ≫
        S.fromSpecStalk (Deformation.Artin.basePoint U u₀)) := by
    simpa [q, properFlatCurvesProjection] using hz
  obtain ⟨b, hb⟩ := hversal A C f hf y.obj z.obj hy' hz' i.hom hi a.hom ha
  refine ⟨ObjectProperty.homMk b, ?_⟩
  apply ObjectProperty.hom_ext
  simpa using hb

private theorem properFlatCurves_openVersality
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) [IsNoetherian S]
    (hS : B.Contains S)
    (hPF : OpenVersalityOf
      (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)) :
    OpenVersalityOf (properFlatCurvesProjection B S hS) := by
  intro U hU x hx u₀ hu hversal
  have hxPF : (cartesianProperFlatProjection B S hS ⋙
      Over.post B.inclusion).obj x.obj = U := by
    simpa [properFlatCurvesProjection] using hx
  have hversalPF := isVersalAt_properFlatCurve_of_curve B S hS U x hx u₀ hversal
  obtain ⟨V, huV, hV⟩ := hPF U hU x.obj hxPF u₀ hu hversalPF
  refine ⟨V, huV, ?_⟩
  intro u hu' huft
  exact isVersalAt_curve_of_properFlatCurve B S hS U x hx u (hV u hu' huft)


private noncomputable def properFlatHomAsCurveHom
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    {X Y : CartesianProperFlatSpaces B integerBase hZ}
    (hX : Space.HasRelativeDimensionLE 1 B integerBase hZ
      X.obj.obj.hom)
    (hY : Space.HasRelativeDimensionLE 1 B integerBase hZ
      Y.obj.obj.hom)
    (f : X ⟶ Y) : properFlatAsCurve B hZ X hX ⟶ properFlatAsCurve B hZ Y hY := by
  refine ⟨f.hom.hom.right, f.hom.hom.left, ?_⟩
  simpa [properFlatAsCurve, properFlatCommaHomAsSpaceMap] using
    properFlatHom_isPullback_spaces B integerBase hZ f

private def curveAsProperFlatSpace
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (X : AlgebraicGeometry.CurveFamily B hZ) :
    CartesianProperFlatSpaces B integerBase hZ := by
  let C : spaceFamilies B integerBase hZ :=
    ⟨X.total, X.base, (curveToBase X)⟩
  let hC : properFlatSpaceObjects B integerBase hZ :=
    ⟨C, ⟨X.finitePresentation, X.flat, X.proper⟩⟩
  exact ⟨hC⟩

private def curveToProperFlat
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase) :
    AlgebraicGeometry.CurveFamily B hZ ⥤
      CartesianProperFlatSpaces B integerBase hZ where
  obj := curveAsProperFlatSpace B hZ
  map {X Y} (f : X ⟶ Y) := by
    let Cx : spaceFamilies B integerBase hZ :=
      ⟨X.total, X.base, (curveToBase X)⟩
    let Cy : spaceFamilies B integerBase hZ :=
      ⟨Y.total, Y.base, (curveToBase Y)⟩
    let m : Cx ⟶ Cy := {
      left := f.totalMap
      right := f.baseMap
      w := by
        have h := congrArg (fun g => g.hom) f.cartesian.w
        change (f.totalMap ≫ Y.toBase).hom =
          (X.toBase ≫ schemeSpaceMap f.baseMap).hom at h
        change f.totalMap.hom ≫ (curveToBase Y) =
          (curveToBase X) ≫ yoneda.map f.baseMap
        calc
          _ = (f.totalMap ≫ Y.toBase).hom := rfl
          _ = (X.toBase ≫ schemeSpaceMap f.baseMap).hom := h
          _ = _ := rfl
    }
    refine {
      hom := { hom := m }
      property := by
        change (spacesProjection B integerBase hZ).IsStronglyCartesian
          m.right m
        apply (AlgebraicGeometry.spacesProjection_isStronglyCartesian_iff m).2
        let hp := AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ
          (schemeSpaceMap f.baseMap) Y.toBase
        let e : X.total ≅ AlgebraicSpaces.fiberProduct B integerBase hZ
            (schemeSpaceMap f.baseMap) Y.toBase :=
          f.cartesian.isoIsPullback _ _ hp.flip
        have he : IsIso e.hom := inferInstance
        have heq : ObjectProperty.homMk
            (CategoryTheory.Limits.pullback.lift Cx.hom m.left.hom m.w.symm) = e.hom := by
          apply hp.hom_ext
          · apply ObjectProperty.hom_ext
            simp only [ObjectProperty.ι_obj, ObjectProperty.FullSubcategory.comp_hom,
              IsPullback.isoIsPullback_hom_snd, e]
            change CategoryTheory.Limits.pullback.lift Cx.hom m.left.hom m.w.symm ≫
              CategoryTheory.Limits.pullback.fst
                (schemeSpaceMap f.baseMap).hom (curveToBase Y) = Cx.hom
            exact CategoryTheory.Limits.pullback.lift_fst _ _ _
          · apply ObjectProperty.hom_ext
            simp only [ObjectProperty.ι_obj, ObjectProperty.FullSubcategory.comp_hom,
              IsPullback.isoIsPullback_hom_fst, e]
            change CategoryTheory.Limits.pullback.lift Cx.hom m.left.hom m.w.symm ≫
              CategoryTheory.Limits.pullback.snd
                (schemeSpaceMap f.baseMap).hom (curveToBase Y) = m.left.hom
            exact CategoryTheory.Limits.pullback.lift_snd _ _ _
        exact heq ▸ he
    }
  map_id := by intros; ext <;> rfl
  map_comp := by intros; ext <;> rfl

private theorem properFlatAsCurve_curveToProperFlat_obj
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (X : AlgebraicGeometry.CurveFamily B hZ) :
    properFlatAsCurve B hZ ((curveToProperFlat B hZ).obj X)
      X.relativeDimensionLE = X := by
  cases X
  rfl

private theorem curveToProperFlat_properFlatAsCurve_obj
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (X : CartesianProperFlatSpaces B integerBase hZ)
    (hDim : Space.HasRelativeDimensionLE 1 B integerBase hZ
      X.obj.obj.hom) :
    (curveToProperFlat B hZ).obj (properFlatAsCurve B hZ X hDim) = X := by
  cases X
  rfl

private noncomputable abbrev curvesOverIntegersProjection
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase) :=
  curvesProjectionOver B hZ ⋙ Over.post B.inclusion

private noncomputable abbrev properFlatOverIntegersProjection
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase) :=
  cartesianProperFlatProjection B integerBase hZ ⋙
    Over.post B.inclusion

private theorem isVersalAt_curve_of_properFlat
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (U : Over (B.obj hZ).obj)
    (x : AlgebraicGeometry.CurveFamily B hZ)
    (hx : (curvesOverIntegersProjection B hZ).obj x = U)
    (u₀ : U.left)
    (hp : Deformation.Artin.IsVersalAt U (properFlatOverIntegersProjection B hZ) u₀
      ((curveToProperFlat B hZ).obj x) (by
        simpa [curvesOverIntegersProjection, properFlatOverIntegersProjection,
          curvesProjectionOver, curveToProperFlat, curveAsProperFlatSpace,
          cartesianProperFlatProjection] using hx)) :
  Deformation.Artin.IsVersalAt U (curvesOverIntegersProjection B hZ) u₀ x hx := by
  let := Deformation.Artin.residueFieldAlgebra U u₀
  intro A C f hf y z hy hz i hi a ha
  let py := (curveToProperFlat B hZ).obj y
  let pz := (curveToProperFlat B hZ).obj z
  have hy' : (properFlatOverIntegersProjection B hZ).obj py =
      Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap ((B.obj hZ).obj.presheaf.stalk
          (Deformation.Artin.basePoint U u₀)) A)) ≫
        (B.obj hZ).obj.fromSpecStalk (Deformation.Artin.basePoint U u₀)) := by
    simpa [py, properFlatOverIntegersProjection, curvesOverIntegersProjection,
      curvesProjectionOver, curveToProperFlat, curveAsProperFlatSpace,
      cartesianProperFlatProjection] using hy
  have hz' : (properFlatOverIntegersProjection B hZ).obj pz =
      Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap ((B.obj hZ).obj.presheaf.stalk
          (Deformation.Artin.basePoint U u₀)) C)) ≫
        (B.obj hZ).obj.fromSpecStalk (Deformation.Artin.basePoint U u₀)) := by
    simpa [pz, properFlatOverIntegersProjection, curvesOverIntegersProjection,
      curvesProjectionOver, curveToProperFlat, curveAsProperFlatSpace,
      cartesianProperFlatProjection] using hz
  let ip : py ⟶ pz := (curveToProperFlat B hZ).map i
  let ap : py ⟶ (curveToProperFlat B hZ).obj x :=
    (curveToProperFlat B hZ).map a
  have hmap_i : ((properFlatOverIntegersProjection B hZ).map ip).left =
      ((curvesOverIntegersProjection B hZ).map i).left := by
    rfl
  have hip : eqToHom (congrArg Over.left hy').symm ≫
      ((properFlatOverIntegersProjection B hZ).map ip).left ≫
        eqToHom (congrArg Over.left hz') =
      Spec.map (CommRingCat.ofHom f.hom.toRingHom) := by
    rw [hmap_i]
    exact hi
  have hmap_a : ((properFlatOverIntegersProjection B hZ).map ap).left =
      ((curvesOverIntegersProjection B hZ).map a).left := by
    rfl
  have hap : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫
      eqToHom (congrArg Over.left hy').symm ≫
      ((properFlatOverIntegersProjection B hZ).map ap).left ≫
      eqToHom (congrArg Over.left (by
        simpa [curvesOverIntegersProjection, properFlatOverIntegersProjection,
          curvesProjectionOver, curveToProperFlat, curveAsProperFlatSpace,
          cartesianProperFlatProjection] using hx)) =
      U.left.fromSpecResidueField u₀ := by
    rw [hmap_a]
    exact ha
  obtain ⟨b, hb⟩ := hp A C f hf py pz hy' hz' ip hip ap hap
  let bc₀ := properFlatHomAsCurveHom B hZ (X := pz)
    (Y := (curveToProperFlat B hZ).obj x) z.relativeDimensionLE x.relativeDimensionLE b
  let bc : z ⟶ x := by
    simpa only [pz, properFlatAsCurve_curveToProperFlat_obj] using bc₀
  refine ⟨bc, ?_⟩
  apply AlgebraicGeometry.CurveFamily.Hom.ext
  · have hbase := congrArg (fun g : py ⟶ (curveToProperFlat B hZ).obj x =>
      g.hom.hom.right) hb
    change (i.baseMap ≫ bc.baseMap) = a.baseMap
    have hbc : bc.baseMap = b.hom.hom.right := by
      cases properFlatAsCurve_curveToProperFlat_obj B hZ z
      cases properFlatAsCurve_curveToProperFlat_obj B hZ x
      rfl
    rw [hbc]
    change (i.baseMap ≫ b.hom.hom.right) = a.baseMap at hbase
    exact hbase
  · have htotal := congrArg (fun g : py ⟶ (curveToProperFlat B hZ).obj x =>
      g.hom.hom.left) hb
    change (i.totalMap ≫ bc.totalMap) = a.totalMap
    have hbc : bc.totalMap = b.hom.hom.left := by
      cases properFlatAsCurve_curveToProperFlat_obj B hZ z
      cases properFlatAsCurve_curveToProperFlat_obj B hZ x
      rfl
    rw [hbc]
    change (i.totalMap ≫ b.hom.hom.left) = a.totalMap at htotal
    exact htotal

private theorem isVersalAt_properFlat_of_curve
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (U : Over (B.obj hZ).obj)
    (x : AlgebraicGeometry.CurveFamily B hZ)
    (hx : (curvesOverIntegersProjection B hZ).obj x = U)
    (u₀ : U.left)
    (hp : Deformation.Artin.IsVersalAt U (curvesOverIntegersProjection B hZ) u₀ x hx)
    (hpEq : (properFlatOverIntegersProjection B hZ).obj
      ((curveToProperFlat B hZ).obj x) = U) :
    Deformation.Artin.IsVersalAt U (properFlatOverIntegersProjection B hZ) u₀
      ((curveToProperFlat B hZ).obj x) hpEq := by
  let := Deformation.Artin.residueFieldAlgebra U u₀
  intro A C f hf y z hy hz i hi a ha
  let qP := properFlatOverIntegersProjection B hZ
  have hyBase : Nonempty (qP.obj y).left := nonempty_left_of_eq_mk (R := A.carrier) hy
  have hzSub : Subsingleton (qP.obj z).left := subsingleton_left_of_eq_mk (R := C.carrier) hz
  have hyDim := properFlat_relativeDimensionLE_of_hom_over B integerBase hZ a x.relativeDimensionLE
  have hzDim := properFlat_relativeDimensionLE_of_artinianArrow B integerBase hZ i hyDim
    hyBase hzSub
  let cy := properFlatAsCurve B hZ y hyDim
  let cz := properFlatAsCurve B hZ z hzDim
  let ix := properFlatHomAsCurveHom B hZ hyDim hzDim i
  have hDimTarget : Space.HasRelativeDimensionLE 1 B integerBase hZ
      (((curveToProperFlat B hZ).obj x).obj.obj.hom) := by
    change Space.HasRelativeDimensionLE 1 B integerBase hZ
      (curveToBase x)
    exact x.relativeDimensionLE
  let ax₀ := properFlatHomAsCurveHom B hZ hyDim hDimTarget a
  have hxCurve : (curvesOverIntegersProjection B hZ).obj x = U := hx
  have hyCurve : (curvesOverIntegersProjection B hZ).obj cy =
      Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap ((B.obj hZ).obj.presheaf.stalk
          (Deformation.Artin.basePoint U u₀)) A)) ≫
        (B.obj hZ).obj.fromSpecStalk (Deformation.Artin.basePoint U u₀)) := by
    simpa [cy, properFlatAsCurve, properFlatOverIntegersProjection,
      curvesOverIntegersProjection, curvesProjectionOver,
      cartesianProperFlatProjection] using hy
  have hzCurve : (curvesOverIntegersProjection B hZ).obj cz =
      Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap ((B.obj hZ).obj.presheaf.stalk
          (Deformation.Artin.basePoint U u₀)) C)) ≫
        (B.obj hZ).obj.fromSpecStalk (Deformation.Artin.basePoint U u₀)) := by
    simpa [cz, properFlatAsCurve, properFlatOverIntegersProjection,
      curvesOverIntegersProjection, curvesProjectionOver,
      cartesianProperFlatProjection] using hz
  let ix' : cy ⟶ cz := properFlatHomAsCurveHom B hZ hyDim hzDim i
  have eX : properFlatAsCurve B hZ ((curveToProperFlat B hZ).obj x) hDimTarget = x := by
    have hdim : hDimTarget = x.relativeDimensionLE := Subsingleton.elim _ _
    have heq : properFlatAsCurve B hZ ((curveToProperFlat B hZ).obj x)
        hDimTarget = properFlatAsCurve B hZ ((curveToProperFlat B hZ).obj x)
          x.relativeDimensionLE := by rw [hdim]
    rw [heq]
    exact properFlatAsCurve_curveToProperFlat_obj B hZ x
  let ax : cy ⟶ x := ax₀ ≫ eqToHom eX
  have hmap_i : ((curvesOverIntegersProjection B hZ).map ix').left =
      ((properFlatOverIntegersProjection B hZ).map i).left := by
    cases curveToProperFlat_properFlatAsCurve_obj B hZ y hyDim
    cases curveToProperFlat_properFlatAsCurve_obj B hZ z hzDim
    rfl
  have hiCurve : eqToHom (congrArg Over.left hyCurve).symm ≫
      ((curvesOverIntegersProjection B hZ).map ix').left ≫
        eqToHom (congrArg Over.left hzCurve) =
      Spec.map (CommRingCat.ofHom f.hom.toRingHom) := by
    rw [hmap_i]
    exact hi
  have haCurve : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫
      eqToHom (congrArg Over.left hyCurve).symm ≫
      ((curvesOverIntegersProjection B hZ).map ax).left ≫
      eqToHom (congrArg Over.left hxCurve) = U.left.fromSpecResidueField u₀ := by
    have hmap_a : ((curvesOverIntegersProjection B hZ).map ax).left =
        ((properFlatOverIntegersProjection B hZ).map a).left := by
      cases eX
      rfl
    rw [hmap_a]
    exact ha
  obtain ⟨bc, hbc⟩ := hp A C f hf cy cz hyCurve hzCurve ix' hiCurve ax haCurve
  have eY : (curveToProperFlat B hZ).obj cy = y := by
    simpa [cy] using curveToProperFlat_properFlatAsCurve_obj B hZ y hyDim
  have eZ : (curveToProperFlat B hZ).obj cz = z := by
    simpa [cz] using curveToProperFlat_properFlatAsCurve_obj B hZ z hzDim
  let F := curveToProperFlat B hZ
  let bp : z ⟶ F.obj x := eqToHom eZ.symm ≫ F.map bc
  refine ⟨bp, ?_⟩
  have hmap_i : F.map ix' = eqToHom eY ≫ i ≫ eqToHom eZ.symm := by
    apply (CategoryTheory.conj_eqToHom_iff_heq (F.map ix') i eY eZ).2
    cases eY
    cases eZ
    rfl
  have hmap_a : F.map ax = eqToHom eY ≫ a := by
    apply (CategoryTheory.conj_eqToHom_iff_heq (F.map ax) a eY rfl).2
    cases eY
    cases eX
    rfl
  have hmap_eq := congrArg F.map hbc
  rw [Functor.map_comp] at hmap_eq
  have hmi : i ≫ eqToHom eZ.symm = eqToHom eY.symm ≫ F.map ix' := by
    rw [hmap_i]
    simp
  have hma : eqToHom eY.symm ≫ F.map ax = a := by
    rw [hmap_a]
    simp
  calc
    i ≫ bp = (i ≫ eqToHom eZ.symm) ≫ F.map bc := by simp [bp, Category.assoc]
    _ = (eqToHom eY.symm ≫ F.map ix') ≫ F.map bc := by rw [hmi]
    _ = eqToHom eY.symm ≫ (F.map ix' ≫ F.map bc) := by simp [Category.assoc]
    _ = eqToHom eY.symm ≫ F.map ax := by rw [← Functor.map_comp, hbc]
    _ = a := hma

private theorem curves_openVersality_of_properFlat
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (hOpen : OpenVersalityOf
      (properFlatOverIntegersProjection B hZ)) :
    OpenVersalityOf (curvesOverIntegersProjection B hZ) := by
  intro U hU x hx u₀ hu hversal
  have hxP : (properFlatOverIntegersProjection B hZ).obj
      ((curveToProperFlat B hZ).obj x) = U := by
    simpa [properFlatOverIntegersProjection, curvesOverIntegersProjection,
      curvesProjectionOver, curveToProperFlat, curveAsProperFlatSpace,
      cartesianProperFlatProjection] using hx
  have hversalP := isVersalAt_properFlat_of_curve B hZ U x hx u₀ hversal hxP
  obtain ⟨V, huV, hV⟩ := hOpen U hU ((curveToProperFlat B hZ).obj x)
    hxP u₀ hu hversalP
  refine ⟨V, huV, ?_⟩
  intro v hv hvft
  exact isVersalAt_curve_of_properFlat B hZ U x hx v (hV v hv hvft)

private theorem sigma_yoneda_ext
    {C : Type*} [Category.{u} C] {V : C} {T : Over V} {W : C}
    {a b : Σ ψ : W ⟶ V, Over.mk ψ ⟶ T} (h : a.2.left = b.2.left) : a = b := by
  rcases a with ⟨ψ, a⟩
  rcases b with ⟨φ, b⟩
  have hh := OverShriek.sigmaMk_eq (yoneda.obj T) (𝟙 T) a b h
  change (⟨ψ, a ≫ 𝟙 T⟩ : Σ ψ : W ⟶ V, Over.mk ψ ⟶ T) = ⟨φ, b ≫ 𝟙 T⟩ at hh
  simpa only [Category.comp_id] using hh

private noncomputable def relocalizedYonedaRepresentableBy
    {C : Type*} [Category.{u} C] {U V : C} (c : V ⟶ U) (T : Over V) :
    ((OverShriek.relocalizePresheafFunctor c).obj (yoneda.obj T)).RepresentableBy
      ((Over.map c).obj T) := by
  refine ⟨?_, ?_⟩
  · intro W
    refine
      { toFun := fun g => ⟨⟨g.left ≫ T.hom, Over.homMk g.left rfl⟩, by
          change (g.left ≫ T.hom) ≫ c = W.hom
          simpa [Category.assoc] using g.w⟩
        invFun := fun x => Over.homMk x.1.2.left (by
          change x.1.2.left ≫ (T.hom ≫ c) = W.hom
          rw [← Category.assoc]
          exact (congrArg (fun t => t ≫ c) x.1.2.w).trans x.2)
        left_inv := fun g => by ext; rfl
        right_inv := by
          intro x
          apply Subtype.ext
          apply sigma_yoneda_ext
          rfl }
  · intro W W' g a
    apply Subtype.ext
    apply sigma_yoneda_ext
    rfl

private noncomputable def relocalizedYonedaIso
    {C : Type*} [Category.{u} C] {U V : C} (c : V ⟶ U) (T : Over V) :
    yoneda.obj ((Over.map c).obj T) ≅
      (OverShriek.relocalizePresheafFunctor c).obj (yoneda.obj T) :=
  Functor.representableByEquiv (relocalizedYonedaRepresentableBy c T)

private noncomputable abbrev relocalizedChartBase
    {C : Type*} [Category.{u} C] {U V : C} (g : V ⟶ U)
    {F : (Over V)ᵒᵖ ⥤ Type u} {T : Over U}
    (f : yoneda.obj T ⟶ (OverShriek.relocalizePresheafFunctor g).obj F) : Over V :=
  Over.mk (yonedaEquiv f).1.1

private noncomputable def relocalizedChartIso
    {C : Type*} [Category.{u} C] {U V : C} (g : V ⟶ U)
    {F : (Over V)ᵒᵖ ⥤ Type u} {T : Over U}
    (f : yoneda.obj T ⟶ (OverShriek.relocalizePresheafFunctor g).obj F) :
    (Over.map g).obj (relocalizedChartBase g f) ≅ T :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 T.left ≫ T.hom = (yonedaEquiv f).1.1 ≫ g
    rw [Category.id_comp]
    exact (yonedaEquiv f).2.symm)

private noncomputable def relocalizedChartMap
    {C : Type*} [Category.{u} C] {U V : C} (g : V ⟶ U)
    {F : (Over V)ᵒᵖ ⥤ Type u} {T : Over U}
    (f : yoneda.obj T ⟶ (OverShriek.relocalizePresheafFunctor g).obj F) :
    yoneda.obj (relocalizedChartBase g f) ⟶ F :=
  yonedaEquiv.symm (yonedaEquiv f).1.2

private theorem relocalizedChartMap_fac
    {C : Type*} [Category.{u} C] {U V : C} (g : V ⟶ U)
    {F : (Over V)ᵒᵖ ⥤ Type u} {T : Over U}
    (f : yoneda.obj T ⟶ (OverShriek.relocalizePresheafFunctor g).obj F) :
    yoneda.map (relocalizedChartIso g f).inv ≫
      (relocalizedYonedaIso g (relocalizedChartBase g f)).hom ≫
        (OverShriek.relocalizePresheafFunctor g).map (relocalizedChartMap g f) = f := by
  apply yonedaEquiv.injective
  change ((OverShriek.relocalizePresheafFunctor g).map
    (relocalizedChartMap g f)).app (Opposite.op T)
      ((relocalizedYonedaIso g (relocalizedChartBase g f)).hom.app (Opposite.op T)
        (𝟙 T ≫ (relocalizedChartIso g f).inv)) = yonedaEquiv f
  rw [Category.id_comp]
  apply Subtype.ext
  change (⟨_, F.map (Over.homMk (𝟙 T.left) rfl :
      Over.mk ((𝟙 T.left) ≫ (yonedaEquiv f).1.1) ⟶
        relocalizedChartBase g f).op (yonedaEquiv f).1.2⟩ :
      Σ a, F.obj (Opposite.op (Over.mk a))) = (yonedaEquiv f).1
  exact OverShriek.sigmaMk_eq_self F (yonedaEquiv f).1.2 _ rfl

private theorem relocalizedYonedaIso_naturality
    {C : Type*} [Category.{u} C] {U V : C} (c : V ⟶ U)
    {T T' : Over V} (f : T ⟶ T') :
    yoneda.map ((Over.map c).map f) ≫ (relocalizedYonedaIso c T').hom =
      (relocalizedYonedaIso c T).hom ≫
        (OverShriek.relocalizePresheafFunctor c).map (yoneda.map f) := by
  ext W a
  apply Subtype.ext
  apply sigma_yoneda_ext
  rfl

private noncomputable abbrev schemeSpaceOverLargerBase
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS') (T : AlgebraicGeometry.BigFppfOver B S hS) :
    SpacesOverSmallerBase B S S' hS hS' g :=
  ⟨Over.mk (yoneda.map (Over.homMk T.hom : (Over.map g).obj T ⟶ Over.mk g)),
    AlgebraicGeometry.isAlgebraicSpace_yoneda B S' hS' ((Over.map g).obj T)⟩

private noncomputable def schemeSpaceOverLargerBaseIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS') (T : AlgebraicGeometry.BigFppfOver B S hS) :
    schemeSpaceOverLargerBase B S S' hS hS' g T ≅
      (smallerBaseEquivalenceData B S S' hS hS' g).1.functor.obj
        (schemeSpace_ T) := by
  let d := smallerBaseEquivalenceData B S S' hS hS' g
  let e := relocalizedYonedaIso g T ≪≫ (d.2.app (schemeSpace_ T)).symm
  refine ObjectProperty.isoMk _ (Over.isoMk e ?_)
  ext W a
  exact spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B S S' hS hS' g
    (schemeSpace_ T) W ((relocalizedYonedaIso g T).hom.app W a)

private theorem schemeSpaceOverLargerBaseIso_naturality
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    {T T' : AlgebraicGeometry.BigFppfOver B S hS} (f : T ⟶ T') :
    yoneda.map ((Over.map g).map f) ≫
        (schemeSpaceOverLargerBaseIso B S S' hS hS' g T').hom.hom.left =
      (schemeSpaceOverLargerBaseIso B S S' hS hS' g T).hom.hom.left ≫
        ((smallerBaseEquivalenceData
          B S S' hS hS' g).1.functor.map (schemeSpaceMap_ f)).hom.left := by
  let d := smallerBaseEquivalenceData B S S' hS hS' g
  change yoneda.map ((Over.map g).map f) ≫
      ((relocalizedYonedaIso g T').hom ≫ d.2.inv.app (schemeSpace_ T')) =
    ((relocalizedYonedaIso g T).hom ≫ d.2.inv.app (schemeSpace_ T)) ≫ _
  rw [← Category.assoc, relocalizedYonedaIso_naturality, Category.assoc,
    Category.assoc]
  congr 1

private noncomputable def schemeSpaceOverLargerBaseMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    {T T' : AlgebraicGeometry.BigFppfOver B S hS} (f : T ⟶ T') :
    schemeSpaceOverLargerBase B S S' hS hS' g T ⟶
      schemeSpaceOverLargerBase B S S' hS hS' g T' :=
  (schemeSpaceOverLargerBaseIso B S S' hS hS' g T).hom ≫
    (smallerBaseEquivalenceData
      B S S' hS hS' g).1.functor.map (schemeSpaceMap_ f) ≫
      (schemeSpaceOverLargerBaseIso B S S' hS hS' g T').inv

private theorem schemeSpaceOverLargerBaseMap_left
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    {T T' : AlgebraicGeometry.BigFppfOver B S hS} (f : T ⟶ T') :
    (schemeSpaceOverLargerBaseMap B S S' hS hS' g f).hom.left =
      yoneda.map ((Over.map g).map f) := by
  let i := schemeSpaceOverLargerBaseIso B S S' hS hS' g T
  let j := schemeSpaceOverLargerBaseIso B S S' hS hS' g T'
  let e := (smallerBaseEquivalenceData
    B S S' hS hS' g).1
  have hn := schemeSpaceOverLargerBaseIso_naturality B S S' hS hS' g f
  change yoneda.map ((Over.map g).map f) ≫ j.hom.hom.left =
    i.hom.hom.left ≫ (e.functor.map (schemeSpaceMap_ f)).hom.left at hn
  change (i.hom.hom.left ≫
    (e.functor.map (schemeSpaceMap_ f)).hom.left) ≫
      j.inv.hom.left = yoneda.map ((Over.map g).map f)
  have hj := congrArg (fun k => k.hom.left) j.hom_inv_id
  change j.hom.hom.left ≫ j.inv.hom.left = 𝟙 _ at hj
  have h := congrArg (fun k => k ≫ j.inv.hom.left) hn.symm
  change (i.hom.hom.left ≫
      (e.functor.map (schemeSpaceMap_ f)).hom.left) ≫
      j.inv.hom.left =
    (yoneda.map ((Over.map g).map f) ≫ j.hom.hom.left) ≫
      j.inv.hom.left at h
  have h_ass :
      (yoneda.map ((Over.map g).map f) ≫ j.hom.hom.left) ≫
          j.inv.hom.left =
        yoneda.map ((Over.map g).map f) ≫
          (j.hom.hom.left ≫ j.inv.hom.left) := Category.assoc _ _ _
  have h_cancel := congrArg
    (fun k => yoneda.map ((Over.map g).map f) ≫ k) hj
  exact h.trans (h_ass.trans (h_cancel.trans (Category.comp_id _)))

end CurvesVersality

end AlgebraicGeometry

end
