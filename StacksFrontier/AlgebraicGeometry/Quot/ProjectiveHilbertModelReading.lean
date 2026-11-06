/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ProjectiveSpaceHilbertModels
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertQuotObjectwise
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertQuotFunctorEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedDefiningIdealSheafObject
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModuleBase
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureProjectionComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureProjectionChartSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackIdIsoTransport
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic
public import StacksFrontier.CategoryTheory.FilteredDerived.Category.Opposite

/-!
# The quotient read in `Hilb_{ℙⁿ_U/U}` from a closed subscheme of `ℙⁿ_T`

Let `U` be an object of the big fppf site over `Spec ℤ` and `T` a scheme over `U`. A point of the
Hilbert functor of `ℙⁿ_U ⟶ U` over `T` is a closed subspace `Z` of the base change
`X_T = ℙⁿ_U ×_U T`, and the model `AlgebraicGeometry.C1590Private.projectiveSpaceHilbertModel`
reads it, through Stacks 0D00 and the reading of modules on `X_T ≅ ℙⁿ_T`, as a quotient of
`𝒪_{ℙⁿ_T}` (`AlgebraicGeometry.C1590Private.modelQuotient`).

If `Z` is the image of a closed immersion of schemes `j : R ⟶ ℙⁿ_T`, that quotient is `j_*𝒪_R`:
the quotient of `𝒪_{X_T}` by the defining ideal sheaf of `Z` is `i_*𝒪_Z` (Stacks 03MB), and the
reading of `i_*𝒪_Z` on `ℙⁿ_T` is the direct image along `j` of the structure sheaf of `R`, the
direct image along a represented affine morphism of the associated module being the associated
module of the direct image (Stacks 03DX).

## Main results

* `AlgebraicGeometry.ProjectiveHilbertModelReading.cokernelDefiningIdealSubobjectIso`.
* `AlgebraicGeometry.ProjectiveHilbertModelReading.yReadingPushforwardStructureSheafIso`.

## References

* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.ProjectiveHilbertModelReading

open Space

section Reading

open C1590Private ProjectiveQuot ProjectiveQuotOverSpace

variable {B : BigFppfSite.{u}} {n : ℕ} {D : QuotSituation B integerBase B.contains_integerBase}
  (E : ProjectiveFrame B n D) (T : SchemesOver D.Y)

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- The represented algebraic space of `ℙⁿ_T`, in the spelling of
`AlgebraicGeometry.C1590Private.yReading`. -/
abbrev projectiveSpaceSpace : AlgebraicSpaces B integerBase B.contains_integerBase :=
  ⟨yoneda.obj (projectiveSite B n T.left), isAlgebraicSpace_yoneda B integerBase
    B.contains_integerBase (projectiveSite B n T.left)⟩

/-- `spaceIso E T` in the spelling of `AlgebraicGeometry.C1590Private.yReading`. -/
abbrev spaceIso' : projectiveSpaceSpace (n := n) T ≅ D.space T :=
  spaceIso E T

/-- The inverse image along `h_{ℙⁿ_T} ≅ X_T` of a direct image along `X_T`'s isomorphism is the
module. -/
def modulePullbackPushforwardSpaceIso
    (N : Space.Modules.{u, u} B integerBase B.contains_integerBase
      (projectiveSpaceSpace (n := n) T).1 (projectiveSpaceSpace (n := n) T).2) :
    (modulePullback B integerBase B.contains_integerBase (spaceIso' E T).hom).obj
        ((modulePushforward B integerBase B.contains_integerBase (spaceIso' E T).hom).obj N) ≅ N :=
  ((modulePushforwardInvIsoModulePullback B integerBase B.contains_integerBase
      (spaceIso' E T)).app _).symm ≪≫
    (modulePushforwardCompIso B integerBase B.contains_integerBase (spaceIso' E T).hom
      (spaceIso' E T).inv).app N ≪≫
    (modulePushforwardIdIsoOfEq B integerBase B.contains_integerBase _
      (spaceIso' E T).hom_inv_id).app N

/-- **The reading of the direct image of the structure sheaf along a represented affine morphism
is the direct image of the structure sheaf of the scheme**: the direct image along `h_R ⟶ h_W` of
`𝒪_{h_R}` is the associated module of `j_*𝒪_R` (Stacks 03DX), and the reading of an associated
quasi-coherent module is the module. -/
def readingPushforwardUnitIso {W R : BigFppfOver B integerBase B.contains_integerBase} (j : R ⟶ W)
    [IsAffineHom (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) j.left)]
    [QuasiCompact (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) j.left)]
    [QuasiSeparated
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) j.left)] :
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj W) W.left.property).obj
      ((representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase W).inverse.obj
        ((modulePushforward B integerBase B.contains_integerBase
          (representedSpaceMap B integerBase B.contains_integerBase j)).obj
          (SheafOfModules.unit (structureRingSheaf B integerBase B.contains_integerBase
            ⟨yoneda.obj R, isAlgebraicSpace_yoneda B integerBase B.contains_integerBase R⟩)))) ≅
      (Scheme.Modules.pushforward
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) j.left)).obj
        (SheafOfModules.unit ((𝒯).obj R).ringCatSheaf) :=
  (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj W) W.left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B integerBase
          B.contains_integerBase W).inverse.mapIso
        (@asIso _ _ _ _ _ (isIso_representedAssociatedModule_structureProjection_target B
          integerBase B.contains_integerBase j)).symm) ≪≫
    representedZariskiModuleQuasicoherentSchemeIso B integerBase B.contains_integerBase W
      ⟨_, ProperCoherentFiniteType.isQuasicoherent_pushforward _ _
        (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _)⟩

/-- **The reading on `ℙⁿ_T` of `i_*𝒪_Z`, for `Z ⊆ X_T` the image of a closed immersion
`j : R ⟶ ℙⁿ_T`, is `j_*𝒪_R`.** -/
def yReadingPushforwardStructureSheafIso {R : BigFppfOver B integerBase B.contains_integerBase}
    (j : R ⟶ projectiveSite B n T.left) [IsClosedImmersion ((𝒯).map j)]
    (hZc : IsClosedSubspace B integerBase B.contains_integerBase
      (Subfunctor.range (yoneda.map j ≫ (spaceIso' E T).hom.hom))) :
    (yReading E T).obj (pushforwardStructureSheaf B integerBase B.contains_integerBase (D.space T)
        ⟨Subfunctor.range (yoneda.map j ≫ (spaceIso' E T).hom.hom), hZc⟩) ≅
      (Scheme.Modules.pushforward ((𝒯).map j)).obj (Stacks.Ample.unitModule ((𝒯).obj R)) := by
  haveI : IsAffineHom
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) j.left) :=
    (inferInstance : IsAffineHom ((𝒯).map j))
  haveI : QuasiCompact
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) j.left) :=
    (inferInstance : QuasiCompact ((𝒯).map j))
  haveI : QuasiSeparated
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) j.left) :=
    (inferInstance : QuasiSeparated ((𝒯).map j))
  set m := yoneda.map j ≫ (spaceIso' E T).hom.hom with hm
  haveI : Mono (yoneda.map j) := by
    have : Mono j := (𝒯).mono_of_mono_map inferInstance
    infer_instance
  haveI : IsIso (spaceIso' E T).hom.hom :=
    Iso.isIso_hom ((ObjectProperty.ι _).mapIso (spaceIso' E T))
  haveI : Mono m := mono_comp' inferInstance (IsIso.mono_of_iso (spaceIso' E T).hom.hom)
  haveI : IsIso (Subfunctor.toRange m) := inferInstance
  let φ := spaceIso' E T
  let RA : AlgebraicSpaces B integerBase B.contains_integerBase :=
    ⟨yoneda.obj R, isAlgebraicSpace_yoneda B integerBase B.contains_integerBase R⟩
  let ZA : AlgebraicSpaces B integerBase B.contains_integerBase :=
    ⟨(Subfunctor.range m).toFunctor, hZc.1⟩
  let ef : RA ≅ ZA :=
    { hom := ObjectProperty.homMk (Subfunctor.toRange m)
      inv := ObjectProperty.homMk (inv (Subfunctor.toRange m))
      hom_inv_id := ObjectProperty.hom_ext _ (IsIso.hom_inv_id (Subfunctor.toRange m))
      inv_hom_id := ObjectProperty.hom_ext _ (IsIso.inv_hom_id (Subfunctor.toRange m)) }
  have h1 : ef.hom ≫ subspaceInclusion B integerBase B.contains_integerBase (D.space T)
      ⟨Subfunctor.range m, hZc⟩ =
        representedSpaceMap B integerBase B.contains_integerBase j ≫ φ.hom :=
    ObjectProperty.hom_ext _ (Subfunctor.toRange_ι m)
  let P1 : pushforwardStructureSheaf B integerBase B.contains_integerBase (D.space T)
        ⟨Subfunctor.range m, hZc⟩ ≅
      (modulePushforward B integerBase B.contains_integerBase φ.hom).obj
        ((modulePushforward B integerBase B.contains_integerBase
          (representedSpaceMap B integerBase B.contains_integerBase j)).obj
          (SheafOfModules.unit (structureRingSheaf B integerBase B.contains_integerBase RA))) :=
    (modulePushforward B integerBase B.contains_integerBase
        (subspaceInclusion B integerBase B.contains_integerBase (D.space T)
          ⟨Subfunctor.range m, hZc⟩)).mapIso
        (@asIso _ _ _ _ _ (isIso_structureProjectionOfHom B integerBase B.contains_integerBase
          ef)) ≪≫
      (modulePushforwardCompIso B integerBase B.contains_integerBase ef.hom _).app _ ≪≫
      eqToIso (congrArg (fun k => (modulePushforward B integerBase B.contains_integerBase k).obj
        (SheafOfModules.unit (structureRingSheaf B integerBase B.contains_integerBase RA))) h1) ≪≫
      ((modulePushforwardCompIso B integerBase B.contains_integerBase
        (representedSpaceMap B integerBase B.contains_integerBase j) φ.hom).app _).symm
  exact (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj (projectiveSite B n T.left)) (projectiveSite B n T.left).left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
        (projectiveSite B n T.left)).inverse.mapIso
        ((modulePullback B integerBase B.contains_integerBase φ.hom).mapIso P1 ≪≫
          modulePullbackPushforwardSpaceIso E T _)) ≪≫
    readingPushforwardUnitIso j

end Reading

section Model

open C1590Private ProjectiveQuot ProjectiveQuotOverSpace

variable {B : BigFppfSite.{u}} {n : ℕ} (U : BigFppfOver B integerBase B.contains_integerBase)

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- The model of the Quot presheaf of `𝒪_{ℙⁿ_U}/ℙⁿ_U/U` reads its sections as the quotients that
Stacks 0D00 attaches to the families of the Hilbert model. -/
theorem projectiveSpaceQuotModel_iso_hom_app {T : BigFppfOver B integerBase B.contains_integerBase}
    (s : (projectiveSpaceQuotModel n U).presheaf.obj (Opposite.op T)) :
    (projectiveSpaceQuotModel n U).iso.hom.app (Opposite.op T) ⟨s⟩ =
      quotFamilyOfHilbertFamilyOver (projectiveSpaceMap n U)
        (isFinitePresentation_projectiveSpaceMap n U)
        ((projectiveSpaceHilbertModel n U).familyEquiv T s) :=
  (Iso.inv_hom_id_app_apply (hilbertPresheafIsoQuotSitePresheaf (projectiveSpaceMap n U)
    (isFinitePresentation_projectiveSpaceMap n U)) (Opposite.op T)
    ((projectiveSpaceQuotModel n U).iso.hom.app (Opposite.op T) ⟨s⟩)).symm

/-- **The quotient read off a family of the Hilbert functor of `ℙⁿ_U ⟶ U` which is the image of a
closed immersion `j : R ⟶ ℙⁿ_T` is `j_*𝒪_R`.** -/
theorem nonempty_quotient_quotKernel_iso {T : BigFppfOver B integerBase B.contains_integerBase}
    (y : HilbertFamilyOver (projectiveSpaceMap n U) T)
    {R : BigFppfOver B integerBase B.contains_integerBase} (j : R ⟶ projectiveSite B n T)
    [IsClosedImmersion ((𝒯).map j)]
    (hZ : y.family.Z = Subfunctor.range (yoneda.map j ≫ (spaceIso' (projectiveSpaceFrame n U)
        (CostructuredArrow.mk (ObjectProperty.homMk y.toBase))).hom.hom)) :
    Nonempty (quotient (quotKernel (hasUnitReading_projectiveSpaceFrame n U)
        (structureSheafTestScheme (CostructuredArrow.mk y.toBase))
        (hilbertFamilySubobject (projectiveSpaceMap n U)
          (isFinitePresentation_projectiveSpaceMap n U) (CostructuredArrow.mk y.toBase)
          y.family)) ≅
      (Scheme.Modules.pushforward ((𝒯).map j)).obj (Stacks.Ample.unitModule ((𝒯).obj R))) := by
  obtain ⟨e1⟩ := C1590Private.nonempty_quotient_quotKernel_iso
    (hasUnitReading_projectiveSpaceFrame n U)
    (structureSheafTestScheme (CostructuredArrow.mk y.toBase))
    (hilbertFamilySubobject (projectiveSpaceMap n U)
      (isFinitePresentation_projectiveSpaceMap n U) (CostructuredArrow.mk y.toBase) y.family)
  have hK := isQuasicoherentOnSite_hilbertFamilyQuotient (projectiveSpaceMap n U)
    (isFinitePresentation_projectiveSpaceMap n U) (CostructuredArrow.mk y.toBase) y.family
  have hepi := epi_yReading_map (projectiveSpaceFrame n U)
    (structureSheafTestScheme (CostructuredArrow.mk y.toBase))
    (hilbertFamilySubobject (projectiveSpaceMap n U)
      (isFinitePresentation_projectiveSpaceMap n U) (CostructuredArrow.mk y.toBase) y.family) hK
  have hZc : IsClosedSubspace B integerBase B.contains_integerBase
      (Subfunctor.range (yoneda.map j ≫ (spaceIso' (projectiveSpaceFrame n U)
        (CostructuredArrow.mk (ObjectProperty.homMk y.toBase))).hom.hom)) :=
    hZ ▸ y.family.closed
  have hZd : (⟨y.family.Z, y.family.closed⟩ :
      ClosedSubspaces B integerBase B.contains_integerBase
        (schemeBaseChangeSpace (projectiveSpaceMap n U) (CostructuredArrow.mk y.toBase)).1) =
      ⟨_, hZc⟩ := Subtype.ext hZ
  exact ⟨e1 ≪≫ @Abelian.cokernelKernelSubobjectIso _ _ _ _ _ _ hepi ≪≫
    (yReading (projectiveSpaceFrame n U)
      (structureSheafTestScheme (CostructuredArrow.mk y.toBase))).mapIso
      (hilbertFamilyQuotientIso (projectiveSpaceMap n U)
        (isFinitePresentation_projectiveSpaceMap n U) (CostructuredArrow.mk y.toBase) y.family) ≪≫
    eqToIso (congrArg (fun Zd => (yReading (projectiveSpaceFrame n U)
      (structureSheafTestScheme (CostructuredArrow.mk y.toBase))).obj
      (pushforwardStructureSheaf B integerBase B.contains_integerBase
        (schemeBaseChangeSpace (projectiveSpaceMap n U) (CostructuredArrow.mk y.toBase))
          Zd)) hZd) ≪≫
    yReadingPushforwardStructureSheafIso (projectiveSpaceFrame n U)
      (structureSheafTestScheme (CostructuredArrow.mk y.toBase)) j hZc⟩

/-- **The quotient a section of the model of `Hilb_{ℙⁿ_U/U}` reads as, when its family is the
image of a closed immersion `j : R ⟶ ℙⁿ_T`, is `j_*𝒪_R`.** -/
theorem nonempty_quotient_modelQuotient_iso {T : BigFppfOver B integerBase B.contains_integerBase}
    (s : (projectiveSpaceQuotModel n U).presheaf.obj (Opposite.op T))
    {R : BigFppfOver B integerBase B.contains_integerBase} (j : R ⟶ projectiveSite B n T)
    [IsClosedImmersion ((𝒯).map j)]
    (hZ : ((projectiveSpaceHilbertModel n U).familyEquiv T s).family.Z =
      Subfunctor.range (yoneda.map j ≫ (spaceIso' (projectiveSpaceFrame n U)
        (CostructuredArrow.mk (ObjectProperty.homMk
          ((projectiveSpaceHilbertModel n U).familyEquiv T s).toBase))).hom.hom)) :
    Nonempty (quotient (modelQuotient n U s).1 ≅
      (Scheme.Modules.pushforward ((𝒯).map j)).obj (Stacks.Ample.unitModule ((𝒯).obj R))) := by
  have hmq : (modelQuotient n U s).1 = quotKernel (hasUnitReading_projectiveSpaceFrame n U)
      (structureSheafTestScheme
        (CostructuredArrow.mk ((projectiveSpaceHilbertModel n U).familyEquiv T s).toBase))
      (hilbertFamilySubobject (projectiveSpaceMap n U)
        (isFinitePresentation_projectiveSpaceMap n U)
        (CostructuredArrow.mk ((projectiveSpaceHilbertModel n U).familyEquiv T s).toBase)
        ((projectiveSpaceHilbertModel n U).familyEquiv T s).family) := by
    have h := quotPairsIso_hom_app_snd (n := n) (U := U) (Opposite.op T)
      ((projectiveSpaceQuotModel n U).iso.hom.app (Opposite.op T) ⟨s⟩)
    refine h.trans ?_
    rw [projectiveSpaceQuotModel_iso_hom_app]
    rfl
  rw [hmq]
  exact nonempty_quotient_quotKernel_iso U _ j hZ

end Model

end AlgebraicGeometry.ProjectiveHilbertModelReading

end
