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
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality.LargerBaseFamilies
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality.ProperFlatFamilies
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality.OverIntegers
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality.Relocalization
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality.LargerBaseFamilies

/-!
# Curves over a scheme as proper flat families

A family of curves over a scheme `S` of the site (an object of the costructured arrow category
of Stacks 0D54) as a finitely presented, flat and proper family of relative dimension at most
one over `S`, the resulting functor `curveOverS_toProperFlatCurves` and its preservation of
pullback squares, and the first of the properties of morphisms preserved by relocalization of
étale charts (presheaf properties, quasi-compactness, separatedness).
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
attribute [local instance] MorphismProperty.IsMultiplicative.toContainsIdentities
attribute [local instance] relocalizePreservesPullbacks

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search
for them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_curvesOverBase
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_curvesOverBase
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_curvesOverBase (B := B) (S := S) (hS := hS)).has_limit _

/-- Products of presheaves on the big fppf site over `S`, given directly (instance search
times out under Lean v4.35.0). -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_curvesOverBase
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {J : Type} :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasLimitsOfShape_discrete_presheaf_over_curvesOverBase
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {J : Type} :
    HasLimitsOfShape (Discrete J) ((Over (B.obj hS))ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

/-- The same shortcut for presheaves on `Over (B.obj hS)`. -/
local instance (priority := high) hasPullbacks_presheaf_over_curvesOverBase
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((Over (B.obj hS))ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_over_curvesOverBase
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (Over (B.obj hS))ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_over_curvesOverBase (B := B) (S := S) (hS := hS)).has_limit _

/-- The structure map of a curve over `S` composes with `S → ℤ` to its base map to `ℤ`. -/
private theorem curveOverS_hom_comp_eq
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    (X : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)) :
    (Over.mk X.hom : AlgebraicGeometry.BigFppfOver B S hS).hom ≫
        (B.inclusion.preimage (specULiftZIsTerminal.from (B.obj hS).1) :
          B.obj hS ⟶ B.obj hZ) =
      X.left.base.hom := by
  apply B.inclusion.map_injective
  apply specULiftZIsTerminal.hom_ext

/-- The base of a curve over `S`, viewed over `ℤ` through `S`, is the base over `ℤ`. -/
private noncomputable def curveOverS_baseIso
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    (X : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)) :
    (Over.map (B.inclusion.preimage (specULiftZIsTerminal.from (B.obj hS).1) :
      B.obj hS ⟶ B.obj hZ)).obj (Over.mk X.hom) ≅ X.left.base :=
  Over.isoMk (Iso.refl _)
    ((Category.id_comp _).trans (curveOverS_hom_comp_eq B hZ S hS X).symm)

/-- The structure map of a curve over `S` as a map of its base to `S`, viewed over `ℤ`. -/
private noncomputable def curveOverS_baseHom
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    (X : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)) :
    X.left.base ⟶ Over.mk (B.inclusion.preimage
      (specULiftZIsTerminal.from (B.obj hS).1) : B.obj hS ⟶ B.obj hZ) :=
  Over.homMk X.hom (curveOverS_hom_comp_eq B hZ S hS X)

/-- The total space of a curve over `S`, as a space over the smaller base `ℤ`. -/
private noncomputable def curveOverS_totalOverSmallerBase
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    (X : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)) :
    SpacesOverSmallerBase B S integerBase hS hZ
      (B.inclusion.preimage (specULiftZIsTerminal.from (B.obj hS).1)) :=
  ⟨Over.mk (curveToBase X.left ≫ yoneda.map (curveOverS_baseHom B hZ S hS X)),
    X.left.total.property⟩

private noncomputable def curveOverS_totalToBase
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    (X : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)) :
    curveOverS_totalOverSmallerBase B hZ S hS X ⟶
      schemeSpaceOverLargerBase B S integerBase hS hZ
        (B.inclusion.preimage (specULiftZIsTerminal.from (B.obj hS).1))
        (Over.mk X.hom) :=
  ObjectProperty.homMk (Over.homMk
    (curveToBase X.left ≫ yoneda.map (curveOverS_baseIso B hZ S hS X).inv) (by
      change (curveToBase X.left ≫ yoneda.map (curveOverS_baseIso B hZ S hS X).inv) ≫
        yoneda.map (Over.homMk X.hom : (Over.map _).obj (Over.mk X.hom) ⟶ Over.mk _) =
        (curveToBase X.left) ≫ yoneda.map (curveOverS_baseHom B hZ S hS X)
      rw [Category.assoc, ← yoneda.map_comp]
      congr 2))

private noncomputable def curveOverS_spaceFamily
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    (X : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)) :
    spaceFamilies B S hS :=
  spaceFamilyOfLargerBase B S integerBase hS hZ _ (Over.mk X.hom)
    (curveOverS_totalOverSmallerBase B hZ S hS X) (curveOverS_totalToBase B hZ S hS X)

private noncomputable def curveOverS_spaceFamily_arrowIso
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    (X : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)) :
    Arrow.mk ((OverShriek.relocalizePresheafFunctor
      ((B.inclusion.preimage (specULiftZIsTerminal.from (B.obj hS).1)) :
        B.obj hS ⟶ B.obj hZ)).map
        (curveOverS_spaceFamily B hZ S hS X).hom) ≅
      Arrow.mk (curveToBase X.left) := by
  let i := curveOverS_baseIso B hZ S hS X
  let a := curveOverS_totalToBase B hZ S hS X
  have hβ : Arrow.mk a.hom.left ≅ Arrow.mk (curveToBase X.left) := by
    refine Arrow.isoMk (Iso.refl _) (yoneda.mapIso i) ?_
    change (curveToBase X.left ≫ yoneda.map i.inv) ≫ yoneda.map i.hom = curveToBase X.left
    rw [Category.assoc, ← yoneda.map_comp, i.inv_hom_id, yoneda.map_id, Category.comp_id]
  exact spaceFamilyOfLargerBase_arrowIso B S integerBase hS hZ _ _ _ a ≪≫ hβ

private noncomputable def curveOverS_asProperFlat
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    (X : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)) :
    CartesianProperFlatSpaces B S hS := by
  let g : B.obj hS ⟶ B.obj hZ :=
    B.inclusion.preimage (specULiftZIsTerminal.from (B.obj hS).1)
  let C := curveOverS_spaceFamily B hZ S hS X
  let f : C.left ⟶ schemeSpace_ C.right := ObjectProperty.homMk C.hom
  let e := curveOverS_spaceFamily_arrowIso B hZ S hS X
  have hfpR : AlgebraicGeometry.Space.IsFinitePresentation B integerBase hZ
      ((OverShriek.relocalizePresheafFunctor g).map f.hom) :=
    finitePresentation_of_arrowIso B integerBase hZ e
      X.left.finitePresentation
  have hfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS f.hom :=
    finitePresentation_of_relocalize B S integerBase hS hZ g f hfpR
  have hflatR : Space.IsFlat B integerBase hZ
      ((OverShriek.relocalizePresheafFunctor g).map f.hom) :=
    holdsOnEveryEtaleChart_of_arrowIso B integerBase hZ
      (@Flat : MorphismProperty Scheme.{u}) e X.left.flat
  have hflat : Space.IsFlat B S hS f.hom :=
    flat_of_relocalize B S integerBase hS hZ g f hflatR
  have hproperR : spaceIsProper B integerBase hZ
      (AlgebraicGeometry.isAlgebraicSpace_viewOver B S integerBase hS hZ g
        C.left.obj C.left.property)
      (AlgebraicGeometry.isAlgebraicSpace_viewOver B S integerBase hS hZ g
        (schemeSpace_ C.right).obj (schemeSpace_ C.right).property)
      ((OverShriek.relocalizePresheafFunctor g).map f.hom) :=
    proper_of_arrowIso B integerBase hZ _ _
      X.left.total.property (schemeSpace_ X.left.base).property
      e X.left.proper
  have hproper : spaceIsProper B S hS C.left.property
      (schemeSpace_ C.right).property C.hom :=
    proper_of_largerBase B S integerBase hS hZ g f hproperR hfp
  exact ⟨⟨C, ⟨hfp, hflat, hproper⟩⟩⟩

private theorem curveOverS_relativeDimensionLE
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    (X : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)) :
    Space.HasRelativeDimensionLE 1 B S hS
      (curveOverS_asProperFlat B hZ S hS X).obj.obj.hom := by
  let g : B.obj hS ⟶ B.obj hZ :=
    B.inclusion.preimage (specULiftZIsTerminal.from (B.obj hS).1)
  let C := curveOverS_spaceFamily B hZ S hS X
  let f : C.left ⟶ schemeSpace_ C.right := ObjectProperty.homMk C.hom
  have hR : Space.HasRelativeDimensionLE 1 B integerBase hZ
      ((OverShriek.relocalizePresheafFunctor g).map f.hom) :=
    relativeDimensionLE_of_arrowIso B integerBase hZ
      (curveOverS_spaceFamily_arrowIso B hZ S hS X)
      X.left.relativeDimensionLE
  change Space.HasRelativeDimensionLE 1 B S hS C.hom
  exact relativeDimensionLE_of_relocalize B S integerBase hS hZ g f hR

private noncomputable def curveOverS_asProperFlatCurve
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    (X : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)) :
    ProperFlatCurves B S hS :=
  ⟨curveOverS_asProperFlat B hZ S hS X, curveOverS_relativeDimensionLE B hZ S hS X⟩

private theorem curveOverS_asProperFlatCurve_projection
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    (X : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)) :
    (properFlatCurvesProjection B S hS).obj
        (curveOverS_asProperFlatCurve B hZ S hS X) =
      (CostructuredArrow.pre (AlgebraicGeometry.curvesProjection B hZ)
        (𝟭 B.Schemes) (B.obj hS) ⋙ Over.post B.inclusion).obj X := by
  rfl

private noncomputable def curveOverS_baseMap
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)}
    (f : X ⟶ Y) : (Over.mk X.hom : AlgebraicGeometry.BigFppfOver B S hS) ⟶
      (Over.mk Y.hom : AlgebraicGeometry.BigFppfOver B S hS) :=
  Over.homMk f.left.baseMap.left (by
    change f.left.baseMap.left ≫ Y.hom = X.hom
    have hw := f.w
    change f.left.baseMap.left ≫ Y.hom =
      X.hom ≫ 𝟙 (B.obj hS) at hw
    simpa only [Category.comp_id] using hw)

/-- The isomorphisms `curveOverS_baseIso` are natural in the curve. -/
private theorem curveOverS_baseMap_comp_baseIso
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)}
    (f : X ⟶ Y) :
    f.left.baseMap ≫ (curveOverS_baseIso B hZ S hS Y).inv =
      (curveOverS_baseIso B hZ S hS X).inv ≫
        (Over.map (B.inclusion.preimage (specULiftZIsTerminal.from (B.obj hS).1) :
          B.obj hS ⟶ B.obj hZ)).map (curveOverS_baseMap B hZ S hS f) :=
  Over.OverMorphism.ext rfl

/-- The total map of a morphism of curves is compatible with the maps to the bases. -/
private theorem curveOverS_totalMap_comp_curveToBase
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)}
    (f : X ⟶ Y) :
    f.left.totalMap.hom ≫ curveToBase Y.left =
      curveToBase X.left ≫ yoneda.map f.left.baseMap :=
  congrArg (fun k => k.hom) f.left.cartesian.w

private noncomputable def curveOverS_totalOverSmallerBaseMap
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)}
    (f : X ⟶ Y) :
    curveOverS_totalOverSmallerBase B hZ S hS X ⟶
      curveOverS_totalOverSmallerBase B hZ S hS Y := by
  have hs : f.left.baseMap ≫ curveOverS_baseHom B hZ S hS Y =
      curveOverS_baseHom B hZ S hS X := by
    apply Over.OverMorphism.ext
    exact (curveOverS_baseMap B hZ S hS f).w
  refine ObjectProperty.homMk (Over.homMk f.left.totalMap.hom ?_)
  change f.left.totalMap.hom ≫
      (curveToBase Y.left ≫ yoneda.map (curveOverS_baseHom B hZ S hS Y)) =
    curveToBase X.left ≫ yoneda.map (curveOverS_baseHom B hZ S hS X)
  rw [← Category.assoc, curveOverS_totalMap_comp_curveToBase, Category.assoc,
    ← yoneda.map_comp, hs]

private theorem curveOverS_totalToBase_naturality
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)}
    (f : X ⟶ Y) :
    curveOverS_totalOverSmallerBaseMap B hZ S hS f ≫
        curveOverS_totalToBase B hZ S hS Y =
      curveOverS_totalToBase B hZ S hS X ≫
        schemeSpaceOverLargerBaseMap B S integerBase hS hZ
          (B.inclusion.preimage (specULiftZIsTerminal.from (B.obj hS).1))
          (curveOverS_baseMap B hZ S hS f) := by
  let g : B.obj hS ⟶ B.obj hZ :=
    B.inclusion.preimage (specULiftZIsTerminal.from (B.obj hS).1)
  let b := curveOverS_baseMap B hZ S hS f
  let iX := curveOverS_baseIso B hZ S hS X
  let iY := curveOverS_baseIso B hZ S hS Y
  have hi := curveOverS_baseMap_comp_baseIso B hZ S hS f
  have hc := curveOverS_totalMap_comp_curveToBase B hZ S hS f
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change f.left.totalMap.hom ≫
      (curveToBase Y.left ≫ yoneda.map iY.inv) =
    (curveToBase X.left ≫ yoneda.map iX.inv) ≫
      (schemeSpaceOverLargerBaseMap B S integerBase hS hZ g b).hom.left
  rw [schemeSpaceOverLargerBaseMap_left]
  calc
    f.left.totalMap.hom ≫ (curveToBase Y.left ≫ yoneda.map iY.inv) =
        (f.left.totalMap.hom ≫ (curveToBase Y.left)) ≫ yoneda.map iY.inv := by
          rw [Category.assoc]
    _ = (curveToBase X.left) ≫ yoneda.map (f.left.baseMap ≫ iY.inv) := by
          rw [hc, yoneda.map_comp, Category.assoc]
    _ = (curveToBase X.left) ≫ yoneda.map (iX.inv ≫ (Over.map g).map b) := by
          rw [hi]
    _ = (curveToBase X.left ≫ yoneda.map iX.inv) ≫
          yoneda.map ((Over.map g).map b) := by
          rw [yoneda.map_comp, Category.assoc]

private noncomputable def curveOverS_spaceFamilyMap
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)}
    (f : X ⟶ Y) :
    curveOverS_spaceFamily B hZ S hS X ⟶
      curveOverS_spaceFamily B hZ S hS Y := by
  let g : B.obj hS ⟶ B.obj hZ :=
    B.inclusion.preimage (specULiftZIsTerminal.from (B.obj hS).1)
  let b := curveOverS_baseMap B hZ S hS f
  let m := curveOverS_totalOverSmallerBaseMap B hZ S hS f
  let aX := curveOverS_totalToBase B hZ S hS X
  let aY := curveOverS_totalToBase B hZ S hS Y
  exact spaceFamilyOfLargerBaseMap B S integerBase hS hZ g
    b aX aY m (curveOverS_totalToBase_naturality B hZ S hS f)

private theorem curveOverS_spaceFamilyMap_right
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)}
    (f : X ⟶ Y) :
    (curveOverS_spaceFamilyMap B hZ S hS f).right =
      curveOverS_baseMap B hZ S hS f := by
  rfl

private theorem curveOverS_spaceFamilyMap_left
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)}
    (f : X ⟶ Y) :
    (curveOverS_spaceFamilyMap B hZ S hS f).left =
      (smallerBaseEquivalenceData B S
        integerBase hS hZ
        (B.inclusion.preimage (specULiftZIsTerminal.from (B.obj hS).1))).1.inverse.map
        (curveOverS_totalOverSmallerBaseMap B hZ S hS f) := by
  rfl

private theorem curveOverS_totalOverSmallerBaseMap_id
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    (X : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)) :
    curveOverS_totalOverSmallerBaseMap B hZ S hS (𝟙 X) =
      𝟙 (curveOverS_totalOverSmallerBase B hZ S hS X) := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  rfl

private theorem curveOverS_totalOverSmallerBaseMap_comp
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    curveOverS_totalOverSmallerBaseMap B hZ S hS (f ≫ g) =
      curveOverS_totalOverSmallerBaseMap B hZ S hS f ≫
        curveOverS_totalOverSmallerBaseMap B hZ S hS g := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  rfl

private noncomputable def curveOverS_spaceFamilyFunctor
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S) :
    CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS) ⥤
      spaceFamilies B S hS where
  obj := curveOverS_spaceFamily B hZ S hS
  map := curveOverS_spaceFamilyMap B hZ S hS
  map_id := by
    intro X
    ext <;> simp [curveOverS_spaceFamilyMap_left,
      curveOverS_spaceFamilyMap_right, curveOverS_totalOverSmallerBaseMap_id]
      <;> rfl
  map_comp := by
    intro X Y Z f g
    ext <;> simp [curveOverS_spaceFamilyMap_left,
      curveOverS_spaceFamilyMap_right, curveOverS_totalOverSmallerBaseMap_comp]
      <;> rfl

private theorem isPullback_spaces_iff
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W X Y Z : AlgebraicSpaces B S hS}
    (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) :
    IsPullback f g h i ↔ IsPullback f.hom g.hom h.hom i.hom := by
  constructor
  · intro hp
    let e := hp.isoIsPullback _ _
      (AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct B S hS h i)
    let e' := (ObjectProperty.ι _).mapIso e
    apply IsPullback.of_iso_pullback ⟨congrArg (fun k => k.hom) hp.w⟩ e'
    · change (e.hom ≫ ObjectProperty.homMk (pullback.fst h.hom i.hom)).hom = f.hom
      simp [e]
    · change (e.hom ≫ ObjectProperty.homMk (pullback.snd h.hom i.hom)).hom = g.hom
      simp [e]
  · exact IsPullback.of_map_of_faithful (ObjectProperty.ι _)

private theorem spaceFamily_stronglyCartesian_of_isPullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A C : spaceFamilies B S hS} (m : A ⟶ C)
    (h : IsPullback m.left.hom A.hom C.hom (yoneda.map m.right)) :
    (spacesProjection B S hS).IsStronglyCartesian m.right m := by
  apply (AlgebraicGeometry.spacesProjection_isStronglyCartesian_iff m).mpr
  let e := h.flip.isoPullback
  have he : (ObjectProperty.ι _).map
      (ObjectProperty.homMk (pullback.lift A.hom m.left.hom m.w.symm) :
        A.left ⟶ AlgebraicSpaces.fiberProduct B S hS
          (schemeSpaceMap m.right) (ObjectProperty.homMk C.hom)) = e.hom := by
    change pullback.lift A.hom m.left.hom m.w.symm = e.hom
    apply pullback.hom_ext
    · simp only [e, pullback.lift_fst, IsPullback.isoPullback_hom_fst]
    · simp only [e, pullback.lift_snd, IsPullback.isoPullback_hom_snd]
  have : IsIso ((ObjectProperty.ι _).map
      (ObjectProperty.homMk (pullback.lift A.hom m.left.hom m.w.symm) :
        A.left ⟶ AlgebraicSpaces.fiberProduct B S hS
          (schemeSpaceMap m.right) (ObjectProperty.homMk C.hom))) := by
    rw [he]
    exact e.isIso_hom
  exact isIso_of_reflects_iso _ (ObjectProperty.ι _)

private theorem spaceFamilyOfLargerBaseMap_isPullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    {T T' : AlgebraicGeometry.BigFppfOver B S hS} (b : T ⟶ T')
    {Z Z' : SpacesOverSmallerBase B S S' hS hS' g}
    (a : Z ⟶ schemeSpaceOverLargerBase B S S' hS hS' g T)
    (a' : Z' ⟶ schemeSpaceOverLargerBase B S S' hS hS' g T')
    (m : Z ⟶ Z')
    (hm : m ≫ a' = a ≫ schemeSpaceOverLargerBaseMap B S S' hS hS' g b)
    (hp : IsPullback m.hom.left a.hom.left a'.hom.left
      (yoneda.map ((Over.map g).map b))) :
    IsPullback (spaceFamilyOfLargerBaseMap B S S' hS hS' g b a a' m hm).left.hom
      (spaceFamilyOfLargerBase B S S' hS hS' g T Z a).hom
      (spaceFamilyOfLargerBase B S S' hS hS' g T' Z' a').hom (yoneda.map b) := by
  let e := (smallerBaseEquivalenceData B S S' hS hS' g).1
  let H := ObjectProperty.ι (fun Y : Over (yoneda.obj (Over.mk g)) =>
    AlgebraicGeometry.IsAlgebraicSpace B S' hS' Y.left) ⋙ Over.forget _
  have hp₀ : IsPullback m a a' (schemeSpaceOverLargerBaseMap B S S' hS hS' g b) := by
    apply IsPullback.of_map H hm
    change IsPullback m.hom.left a.hom.left a'.hom.left
      (schemeSpaceOverLargerBaseMap B S S' hS hS' g b).hom.left
    rw [schemeSpaceOverLargerBaseMap_left]
    exact hp
  let I := schemeSpaceOverLargerBaseIso B S S' hS hS' g T
  let I' := schemeSpaceOverLargerBaseIso B S S' hS hS' g T'
  let c := schemeSpaceMap_ b
  have hp₁ : IsPullback m (a ≫ I.hom) (a' ≫ I'.hom) (e.functor.map c) := by
    apply hp₀.of_iso (Iso.refl _) (Iso.refl _) I I'
    · simp
    · simp
    · simp
    · simp [schemeSpaceOverLargerBaseMap, I, I', e, c, Category.assoc]
  have hp₂ := hp₁.map e.inverse
  have hp₃ : IsPullback (e.inverse.map m)
      (e.inverse.map (a ≫ I.hom) ≫ e.unitIso.inv.app _)
      (e.inverse.map (a' ≫ I'.hom) ≫ e.unitIso.inv.app _) c := by
    apply hp₂.of_iso (Iso.refl _) (Iso.refl _)
      (e.unitIso.app (schemeSpace_ T)).symm
      (e.unitIso.app (schemeSpace_ T')).symm
    · simp
    · simp
    · simp
    · exact e.unitIso.inv.naturality c
  exact (isPullback_spaces_iff B S hS _ _ _ _).mp hp₃

private theorem curveOverS_spaceFamilyMap_isPullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)}
    (f : X ⟶ Y) :
    IsPullback (curveOverS_spaceFamilyMap B hZ S hS f).left.hom
      (curveOverS_spaceFamily B hZ S hS X).hom
      (curveOverS_spaceFamily B hZ S hS Y).hom
      (yoneda.map (curveOverS_baseMap B hZ S hS f)) := by
  apply spaceFamilyOfLargerBaseMap_isPullback _ _ _ _ _ _ _ _ _ _
    (curveOverS_totalToBase_naturality B hZ S hS f)
  let iX := curveOverS_baseIso B hZ S hS X
  let iY := curveOverS_baseIso B hZ S hS Y
  have hp := (isPullback_spaces_iff B integerBase hZ _ _ _ _).mp f.left.cartesian
  apply hp.of_iso (Iso.refl _) (Iso.refl _)
    (yoneda.mapIso iX.symm) (yoneda.mapIso iY.symm)
  · simp; rfl
  · simp; rfl
  · simp; rfl
  · change yoneda.map f.left.baseMap ≫ yoneda.map iY.inv =
      yoneda.map iX.inv ≫ yoneda.map ((Over.map _).map (curveOverS_baseMap B hZ S hS f))
    rw [← yoneda.map_comp, ← yoneda.map_comp, curveOverS_baseMap_comp_baseIso]

private noncomputable def curveOverS_toProperFlatCurves
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S) :
    CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS) ⥤
      ProperFlatCurves B S hS where
  obj := curveOverS_asProperFlatCurve B hZ S hS
  map f := ObjectProperty.homMk
    ⟨ObjectProperty.homMk (curveOverS_spaceFamilyMap B hZ S hS f),
      spaceFamily_stronglyCartesian_of_isPullback B S hS _
        (curveOverS_spaceFamilyMap_isPullback B hZ S hS f)⟩
  map_id X := by
    apply ObjectProperty.hom_ext
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    exact (curveOverS_spaceFamilyFunctor B hZ S hS).map_id X
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    exact (curveOverS_spaceFamilyFunctor B hZ S hS).map_comp f g

private theorem relocalize_faithful
    {C : Type*} [Category.{u} C] {U V : C} (g : V ⟶ U) :
    (OverShriek.relocalizePresheafFunctor g).Faithful := by
  let F := OverShriek.presheafFunctorToOver (U := V)
  let G := OverShriek.presheafFunctorToOver (U := U)
  let : (OverShriek.presheafFunctorToOver (U := V)).IsEquivalence :=
    (OverShriek.presheafEquivalence (U := V)).isEquivalence_functor
  let : (OverShriek.presheafFunctorToOver (U := U)).IsEquivalence :=
    (OverShriek.presheafEquivalence (U := U)).isEquivalence_functor
  let : (Over.map (yoneda.map g)).Faithful := ⟨by
    intro X Y f f' h
    have hh := congrArg (fun k => k.left) h
    exact Over.OverMorphism.ext hh⟩
  exact Functor.Faithful.of_comp_iso (OverShriek.relocalizePresheafFunctorToOverIso g)

attribute [local instance] relocalize_faithful

private theorem relocalizedChartMap_fac'
    {C : Type*} [Category.{u} C] {U V : C} (g : V ⟶ U)
    {F : (Over V)ᵒᵖ ⥤ Type u} {T : Over U}
    (f : yoneda.obj T ⟶ (OverShriek.relocalizePresheafFunctor g).obj F) :
    (relocalizedYonedaIso g (relocalizedChartBase g f)).hom ≫
      (OverShriek.relocalizePresheafFunctor g).map (relocalizedChartMap g f) =
        yoneda.map (relocalizedChartIso g f).hom ≫ f := by
  have hh := congrArg (fun k => yoneda.map (relocalizedChartIso g f).hom ≫ k)
    (relocalizedChartMap_fac g f)
  simpa only [← Category.assoc, ← yoneda.map_comp,
    Iso.hom_inv_id, yoneda.map_id, Category.id_comp] using hh

private noncomputable def relocalizedChartHom
    {C : Type*} [Category.{u} C] {U V : C} (g : V ⟶ U)
    {F G : (Over V)ᵒᵖ ⥤ Type u} (f : F ⟶ G) {T T' : Over U}
    (a : yoneda.obj T ⟶ (OverShriek.relocalizePresheafFunctor g).obj F)
    (b : yoneda.obj T' ⟶ (OverShriek.relocalizePresheafFunctor g).obj G)
    (h : T ⟶ T')
    (hw : yoneda.map h ≫ b = a ≫ (OverShriek.relocalizePresheafFunctor g).map f) :
    relocalizedChartBase g a ⟶ relocalizedChartBase g b := by
  refine Over.homMk h.left ?_
  have hh := congrArg yonedaEquiv hw
  rw [← yonedaEquiv_naturality, yonedaEquiv_comp] at hh
  exact congrArg (fun s => s.1.1) hh

private theorem relocalizedChartHom_comm
    {C : Type*} [Category.{u} C] {U V : C} (g : V ⟶ U)
    {F G : (Over V)ᵒᵖ ⥤ Type u} (f : F ⟶ G) {T T' : Over U}
    (a : yoneda.obj T ⟶ (OverShriek.relocalizePresheafFunctor g).obj F)
    (b : yoneda.obj T' ⟶ (OverShriek.relocalizePresheafFunctor g).obj G)
    (h : T ⟶ T')
    (hw : yoneda.map h ≫ b = a ≫ (OverShriek.relocalizePresheafFunctor g).map f) :
    yoneda.map (relocalizedChartHom g f a b h hw) ≫ relocalizedChartMap g b =
      relocalizedChartMap g a ≫ f := by
  let R := OverShriek.relocalizePresheafFunctor g
  let h' := relocalizedChartHom g f a b h hw
  have hb : (Over.map g).map h' ≫ (relocalizedChartIso g b).hom =
      (relocalizedChartIso g a).hom ≫ h := by
    apply Over.OverMorphism.ext
    change h.left ≫ 𝟙 _ = 𝟙 _ ≫ h.left
    simp
  apply R.map_injective
  apply (cancel_epi (relocalizedYonedaIso g (relocalizedChartBase g a)).hom).mp
  simp only [Functor.map_comp, ← Category.assoc]
  rw [← relocalizedYonedaIso_naturality]
  simp only [Category.assoc]
  rw [relocalizedChartMap_fac', ← Category.assoc, ← yoneda.map_comp, hb,
    yoneda.map_comp, Category.assoc, hw]
  rw [← Category.assoc, ← relocalizedChartMap_fac']
  exact Category.assoc _ _ _

private theorem holdsOnEveryEtaleChart_relocalize
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS') (P : MorphismProperty Scheme.{u})
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : Space.HoldsOnEveryEtaleChart B S hS P f.hom) :
    Space.HoldsOnEveryEtaleChart B S' hS' P
      ((OverShriek.relocalizePresheafFunctor g).map f.hom) := by
  intro U V a b h ha hb hw
  let U' := relocalizedChartBase g a
  let V' := relocalizedChartBase g b
  let a' := relocalizedChartMap g a
  let b' := relocalizedChartMap g b
  let h' := relocalizedChartHom g f.hom a b h hw
  have ha' : (MorphismProperty.inverseImage (@Etale.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a' := by
    apply (presheaf_property_relocalize_iff B S S' hS hS' g (@Etale.{u}) U' X a').mp
    rw [relocalizedChartMap_fac']
    exact MorphismProperty.RespectsIso.precomp _ (yoneda.map (relocalizedChartIso g a).hom) a ha
  have hb' : (MorphismProperty.inverseImage (@Etale.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf b' := by
    apply (presheaf_property_relocalize_iff B S S' hS hS' g (@Etale.{u}) V' Y b').mp
    rw [relocalizedChartMap_fac']
    exact MorphismProperty.RespectsIso.precomp _ (yoneda.map (relocalizedChartIso g b).hom) b hb
  exact hf U' V' a' b' h' ha' hb' (relocalizedChartHom_comm g f.hom a b h hw)

private theorem presheaf_property_relocalize
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : (P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f) :
    (P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S' hS')).presheaf
      ((OverShriek.relocalizePresheafFunctor g).map f) := by
  let R := OverShriek.relocalizePresheafFunctor g
  apply MorphismProperty.relative.of_exists
  intro T a
  let U := relocalizedChartBase g a
  let a' := relocalizedChartMap g a
  obtain ⟨W, b, c, hp⟩ := hf.1 a'
  let b' := (Over.map g).map b ≫ (relocalizedChartIso g a).hom
  let c' := (relocalizedYonedaIso g W).hom ≫ R.map c
  have hp' : IsPullback c' (yoneda.map b') (R.map f) a := by
    apply (hp.map R).of_iso (relocalizedYonedaIso g W).symm (Iso.refl _)
      ((relocalizedYonedaIso g U).symm ≪≫ yoneda.mapIso (relocalizedChartIso g a))
      (Iso.refl _)
    · simp [c']
    · dsimp [b']
      rw [yoneda.map_comp, ← Category.assoc]
      have hn := relocalizedYonedaIso_naturality g b
      simpa only [U, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc] using
        congrArg (fun k => (relocalizedYonedaIso g W).inv ≫ k ≫
          (relocalizedYonedaIso g U).inv ≫ yoneda.map (relocalizedChartIso g a).hom) hn.symm
    · simp
    · simp only [Iso.refl_hom, Category.comp_id, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_hom]
      rw [Category.assoc, ← relocalizedChartMap_fac']
      simp
      rfl
  refine ⟨(Over.map g).obj W, c', b', hp', ?_⟩
  have hb := hf.2 a' c b hp
  simpa [b', relocalizedChartIso, AlgebraicGeometry.BigFppfOver.toScheme,
    AlgebraicGeometry.BigFppfOver.forget] using hb

private theorem quasiCompact_relocalize
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    [MorphismProperty.IsLocalAtTarget (@Surjective.{u}) Scheme.fppfPrecoverage]
    {F G : AlgebraicSpaces B S hS} (f : F ⟶ G)
    (hf : AlgebraicGeometry.Space.IsQuasiCompact B S hS f.hom) :
    AlgebraicGeometry.Space.IsQuasiCompact B S' hS'
      ((OverShriek.relocalizePresheafFunctor g).map f.hom) := by
  intro Z hZ hZqc a
  let R := OverShriek.relocalizePresheafFunctor g
  obtain ⟨X, e, b, hb⟩ := exists_space_over_relocalized B S S' hS hS' g G Z hZ a
  have hXqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS X.obj :=
    (isQuasiCompact_relocalize_iff B S S' hS hS' g X).mp
      (Space.isQuasiCompactSpace_of_iso B S' hS' e.symm hZqc)
  have hP := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS b.hom f.hom
    X.property F.property G.property
  have hp := (IsPullback.of_hasPullback b.hom f.hom).map R
  have hp' : IsPullback (R.map (pullback.fst b.hom f.hom) ≫ e.hom)
      (R.map (pullback.snd b.hom f.hom)) a (R.map f.hom) := by
    apply hp.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    · simp
    · simp
    · simpa using hb.symm
    · simp
  exact Space.isQuasiCompactSpace_of_iso B S' hS' hp'.isoPullback
    ((isQuasiCompact_relocalize_iff B S S' hS hS' g ⟨_, hP⟩).mpr
      (hf X.obj X.property hXqc b.hom))

private theorem separated_relocalize
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    {F G : AlgebraicSpaces B S hS} (f : F ⟶ G)
    (hf : AlgebraicGeometry.Space.IsSeparated B S hS f.hom) :
    AlgebraicGeometry.Space.IsSeparated B S' hS'
      ((OverShriek.relocalizePresheafFunctor g).map f.hom) := by
  let R := OverShriek.relocalizePresheafFunctor g
  let Q := (MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S' hS')).presheaf
  let e := (IsPullback.of_hasPullback f.hom f.hom).map R |>.isoPullback
  have he : R.map (pullback.diagonal f.hom) ≫ e.hom =
      pullback.diagonal (R.map f.hom) := by
    apply pullback.hom_ext <;> simp [e, ← R.map_comp]
  have hq : Q (R.map (pullback.diagonal f.hom)) :=
    presheaf_property_relocalize B S S' hS hS' g
      (@AlgebraicGeometry.IsClosedImmersion.{u}) (pullback.diagonal f.hom) hf
  change Q (pullback.diagonal (R.map f.hom))
  rw [← he]
  exact MorphismProperty.RespectsIso.postcomp _ e.hom _ hq

end CurvesVersality

end AlgebraicGeometry

end
