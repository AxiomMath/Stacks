module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedPicardFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModuleBase
public import StacksFrontier.AlgebraicGeometry.Quot.PicardDescent.InvertibleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist

/-!
# The polarized families of the relatively ample locus: essential surjectivity

Fix an object `X₀ ⟶ V₀` of `Spaces'_{fp, flat, proper}` over the big fppf site of `Spec(ℤ)`,
and a polarized family `(Z ⟶ T, M)` together with a cartesian morphism from `Z ⟶ T` to `X₀ ⟶ V₀`
in `Spaces'_{fp, flat, proper}`. The cartesian square identifies `yoneda Z` with the base change
`X_T`, and the polarization `M`, a quasi-coherent module on `Z`, is the reading of a
quasi-coherent module `N` on `yoneda Z` (Stacks 03DX (2)); its inverse image along `X_T ≅ yoneda Z`
is an invertible module on `X_T` which is ample on `X_T/T`, since its reading on `Z` is `M`
(Stacks 0D32). This produces an object of the relatively ample locus of `Picardstack_{X₀/V₀}`
whose polarized family over `X₀` is isomorphic to the given one: the functor
`AlgebraicGeometry.amplePolarizedFunctor` is essentially surjective.

## Main definitions

* `AlgebraicGeometry.essTest`: the test scheme `T ⟶ V₀`.
* `AlgebraicGeometry.essIso`: the identification `yoneda Z ≅ X_T`.
* `AlgebraicGeometry.essObject`: the object of the Picard stack of a polarized family over `X₀`.
* `AlgebraicGeometry.essPolarizedHom`: the comparison of its polarized family with the given one.
* `AlgebraicGeometry.amplePolarizedEquivalence`: the relatively ample locus of
  `Picardstack_{X₀/V₀}` is equivalent to the category of polarized families over `X₀`.

## Main results

* `AlgebraicGeometry.picardAmple_essObject`: the object lies in the relatively ample locus.
* `AlgebraicGeometry.essSurj_amplePolarizedFunctor`: the functor is essentially surjective.

## References

* [Stacks Project, Tag 0D41](https://stacks.math.columbia.edu/tag/0D41)
* [Stacks Project, Tag 0D32](https://stacks.math.columbia.edu/tag/0D32)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {X₀ : CartesianProperFlatSpaces B integerBase B.contains_integerBase}
  {hc : Space.ModulePushforwardCoherence B integerBase B.contains_integerBase}

variable (c : CostructuredArrow (forgetPolarization B) X₀)

/-- The test scheme over `V₀` of a polarized family over `X₀`: its base, with the morphism of
bases of its cartesian morphism to `X₀ ⟶ V₀`. -/
def essTest : (properFlatPicardSituation X₀).SchemesOver :=
  CostructuredArrow.mk (Y := (schemeOverIntegers B).obj c.left.base)
    ((schemeSpaceFunctor B integerBase B.contains_integerBase).map c.hom.hom.hom.right)

/-- The cartesian square of a polarized family over `X₀`, by Stacks 04U9. -/
theorem isPullback_essSquare :
    IsPullback c.hom.hom.hom.left (schemeSpaceMap c.left.structureMapOverIntegers)
      (commaHomAsSpaceMap X₀.obj.obj) (schemeSpaceMap c.hom.hom.hom.right) :=
  isPullback_commaHomAsSpaceMap_of_isStronglyCartesian B integerBase B.contains_integerBase
    c.hom.hom.hom c.hom.property

/-- The identification of the total space of a polarized family over `X₀` with the base change
of `X₀` to its test scheme. -/
def essIso : schemeSpace ((schemeOverIntegers B).obj c.left.totalObj) ≅
    (properFlatPicardSituation X₀).baseChange (essTest c) :=
  (isPullback_essSquare c).isoIsPullback _ _
    (AlgebraicSpaces.isPullback_fiberProduct B integerBase B.contains_integerBase
      (properFlatPicardSituation X₀).f
      ((Space.schemesOverToOver (properFlatPicardSituation X₀).base).obj (essTest c)).hom)

/-- The identification `yoneda Z ≅ X_T` followed by the projection `X_T ⟶ X₀` is the map of total
spaces of the cartesian morphism. -/
theorem essIso_hom_baseChangeProjection :
    (essIso c).hom ≫ Space.baseChangeProjection (properFlatPicardSituation X₀).f (essTest c) =
      c.hom.hom.hom.left :=
  IsPullback.isoIsPullback_hom_fst _ _ (isPullback_essSquare c) _

/-- The identification `yoneda Z ≅ X_T` followed by the inclusion `X_T ⟶ T` is the structure
morphism of the polarized family. -/
theorem essIso_hom_baseChangeInclusion :
    (essIso c).hom ≫ Space.baseChangeInclusion (properFlatPicardSituation X₀).f (essTest c) =
      schemeSpaceMap c.left.structureMapOverIntegers :=
  IsPullback.isoIsPullback_hom_snd _ _ (isPullback_essSquare c) _

/-! ### The module on `X_T` -/

/-- The total space of a polarized family over `X₀`, as an object of the big fppf site of the
terminal scheme. -/
abbrev essTotal : BigFppfOver B integerBase B.contains_integerBase :=
  (schemeOverIntegers B).obj c.left.totalObj

/-- The polarization of a polarized family is quasi-coherent. -/
theorem isQuasicoherent_essPolarization : c.left.lineBundle.IsQuasicoherent :=
  have : Stacks.Ample.IsInvertibleModule c.left.total c.left.lineBundle := c.left.invertible
  Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _

/-- The polarization of a polarized family, as a quasi-coherent module on its total space. -/
abbrev essPolarizationQcoh :
    (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj
        (essTotal c)).ringCatSheaf).FullSubcategory :=
  ⟨c.left.lineBundle, isQuasicoherent_essPolarization c⟩

/-- **The module on the represented algebraic space of the total space** whose reading on the
total space is the polarization (Stacks 03DX (2)). -/
abbrev essModule :
    Space.Modules.{u, u} B integerBase B.contains_integerBase (yoneda.obj (essTotal c))
      (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase _) :=
  ((Space.representedQuasicoherentSchemeEquivalence B integerBase B.contains_integerBase
    (essTotal c)).functor.obj (essPolarizationQcoh c)).obj

/-- The module on the represented algebraic space of the total space is quasi-coherent. -/
theorem isQuasicoherentOnSite_essModule : (essModule c).IsQuasicoherentOnSite :=
  ((Space.representedQuasicoherentSchemeEquivalence B integerBase B.contains_integerBase
    (essTotal c)).functor.obj (essPolarizationQcoh c)).property

/-- The reading of the module on the total space is the polarization. -/
def essModuleZariskiIso :
    Space.representedZariskiModule B integerBase B.contains_integerBase (essTotal c)
      (essModule c) ≅ c.left.lineBundle :=
  Space.representedZariskiModuleQuasicoherentSchemeIso B integerBase B.contains_integerBase
    (essTotal c) (essPolarizationQcoh c)

/-- The module on the represented algebraic space of the total space is invertible. -/
theorem isInvertibleModule_essModule :
    Space.IsInvertibleModule (schemeSpace (essTotal c)) (essModule c) := by
  have : Stacks.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj
        (essTotal c)).zariskiRingedSite.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj
          (essTotal c)).zariskiRingedSite.O).property c.left.lineBundle := c.left.invertible
  have h1 : RingedSite.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj
        (essTotal c)).zariskiRingedSite c.left.lineBundle 1 :=
    RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible' _ _
      (Stacks.Picard.ZariskiSite.schemeRingedSite_isLocallyRinged _)
  have h2 := SmallEtale.isFiniteLocallyFreeOfRank_associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj (essTotal c))
    (essTotal c).left.property c.left.lineBundle 1 h1
  exact (Space.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one _).2
    ((Space.isFiniteLocallyFreeOfRank_representedSmallEtaleModule_iff B integerBase
      B.contains_integerBase (essTotal c) _ 1).2 h2)

/-- **The module on `X_T`**: the inverse image of the module on the total space along
`X_T ≅ yoneda Z`. -/
abbrev essLineBundle :
    Space.Modules.{u, u} B integerBase B.contains_integerBase
      ((properFlatPicardSituation X₀).baseChange (essTest c)).1
      ((properFlatPicardSituation X₀).baseChange (essTest c)).2 :=
  (Space.modulePullback B integerBase B.contains_integerBase (essIso c).inv).obj (essModule c)

/-- **The object of the Picard stack of a polarized family over `X₀`**: its test scheme, with the
invertible module on `X_T`. -/
def essObject : Space.PicardObject (properFlatPicardSituation X₀) where
  T := essTest c
  lineBundle := essLineBundle c
  invertible := Space.modulePullbackInvertible _ _ (isInvertibleModule_essModule c)

variable (hc) in
/-- The reading of the module on `X_T` on the total space is the polarization. -/
def essBaseChangeModuleIso :
    Space.baseChangeModule B integerBase B.contains_integerBase (essLineBundle c) (essTotal c)
        (essIso c).hom.hom ≅ c.left.lineBundle :=
  Space.restrictToChartSchemeIdEtaleChartIso B integerBase B.contains_integerBase (essTotal c)
      ((Space.modulePullback B integerBase B.contains_integerBase (essIso c).hom).obj
        (essLineBundle c)) ≪≫
    (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj (essTotal c))
        (essTotal c).left.property).mapIso
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
        (essTotal c)).inverse.mapIso
          ((hc.modulePullbackEquivalence (essIso c).symm).unitIso.app (essModule c)).symm) ≪≫
    essModuleZariskiIso c

/-- The structure morphism of the polarized family is the morphism `yoneda Z ≅ X_T ⟶ T` read on
schemes. -/
theorem preimage_essIso_comp_inclusion :
    yoneda.preimage ((essIso c).hom.hom ≫
        (Space.baseChangeInclusion (properFlatPicardSituation X₀).f (essTest c)).hom ≫
          (Iso.refl (yoneda.obj (essTest c).left)).hom) =
      c.left.structureMapOverIntegers := by
  apply yoneda.map_injective
  rw [Functor.map_preimage]
  exact (congrArg (fun k => (essIso c).hom.hom ≫ k) (Category.comp_id _)).trans
    (congrArg (fun k => k.hom) (essIso_hom_baseChangeInclusion c))

variable (hc) in
/-- **The module on `X_T` is ample on `X_T/T`** (Stacks 0D32). -/
theorem picardAmple_essObject :
    Space.picardAmple hc (properFlatPicardSituation X₀) (essObject c) := by
  have : Stacks.Ample.IsInvertibleModule
      ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj (essTotal c))
      c.left.lineBundle := c.left.invertible
  have : Stacks.Ample.IsInvertibleModule c.left.total c.left.lineBundle := c.left.invertible
  have hL : Stacks.Ample.IsInvertibleModule
      ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj (essTotal c))
      (Space.baseChangeModule B integerBase B.contains_integerBase (essLineBundle c)
        (essTotal c) (essIso c).hom.hom) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ (essBaseChangeModuleIso hc c).symm
  refine Space.isRelativelyAmple_of_exists_scheme _ _ (essObject c).invertible
    (essTest c).left (Iso.refl _)
    ⟨essTotal c, (ObjectProperty.ι _).mapIso (essIso c), hL, ?_⟩
  have : Stacks.Ample.IsInvertibleModule c.left.total
      (Space.baseChangeModule B integerBase B.contains_integerBase (essLineBundle c)
        (essTotal c) (essIso c).hom.hom) := hL
  have hamp : @Stacks.RelativeAmple.IsRelativelyAmple _ _
      ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map
        c.left.structureMapOverIntegers)
      (Space.baseChangeModule B integerBase B.contains_integerBase (essLineBundle c)
        (essTotal c) (essIso c).hom.hom) hL :=
    (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _
      (essBaseChangeModuleIso hc c).symm).mp c.left.relativelyAmple
  exact (congrArg (fun k => @Stacks.RelativeAmple.IsRelativelyAmple _ _
    ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map k)
      (Space.baseChangeModule B integerBase B.contains_integerBase (essLineBundle c)
        (essTotal c) (essIso c).hom.hom) hL) (preimage_essIso_comp_inclusion c)).mpr hamp

/-! ### The comparison with the given family -/

variable (hc) in
/-- The comparison of the scheme model of the object of the Picard stack of a polarized family
over `X₀` with the total space of that family. -/
def essTotalMap : ampleModel (picardAmple_essObject hc c) ⟶ essTotal c :=
  yoneda.preimage ((ampleModelIso (picardAmple_essObject hc c)).hom ≫ (essIso c).inv.hom)

variable (hc) in
/-- The comparison of total spaces, read on algebraic spaces, is the identification of the scheme
model followed by `X_T ≅ yoneda Z`. -/
theorem schemeSpaceMap_essTotalMap :
    schemeSpaceMap (essTotalMap hc c) =
      (ampleModelSpaceIso (picardAmple_essObject hc c)).hom ≫ (essIso c).inv :=
  ObjectProperty.hom_ext _ (yoneda.map_preimage _)

variable (hc) in
/-- The comparison of total spaces commutes with the structure morphisms. -/
theorem essTotalMap_comp_structureMap :
    essTotalMap hc c ≫ c.left.structureMapOverIntegers =
      ampleModelHom (picardAmple_essObject hc c) ≫ (integerNormIso (essTest c).left).hom := by
  let F := schemeSpaceFunctor B integerBase B.contains_integerBase
  have e1 : F.map (essTotalMap hc c) =
      (ampleModelSpaceIso (picardAmple_essObject hc c)).hom ≫ (essIso c).inv :=
    schemeSpaceMap_essTotalMap hc c
  have e2 : F.map c.left.structureMapOverIntegers = (essIso c).hom ≫
      Space.baseChangeInclusion (properFlatPicardSituation X₀).f (essTest c) :=
    (essIso_hom_baseChangeInclusion c).symm
  have h1 : F.map (essTotalMap hc c ≫ c.left.structureMapOverIntegers) =
      (ampleModelSpaceIso (picardAmple_essObject hc c)).hom ≫
        Space.baseChangeInclusion (properFlatPicardSituation X₀).f (essTest c) :=
    (F.map_comp _ _).trans ((congrArg₂ (fun a b => a ≫ b) e1 e2).trans
      ((Category.assoc _ _ _).trans (congrArg (fun k =>
        (ampleModelSpaceIso (picardAmple_essObject hc c)).hom ≫ k)
          (Iso.inv_hom_id_assoc _ _))))
  have h2 : F.map (ampleModelHom (picardAmple_essObject hc c) ≫
      (integerNormIso (essTest c).left).hom) =
      (ampleModelSpaceIso (picardAmple_essObject hc c)).hom ≫
        Space.baseChangeInclusion (properFlatPicardSituation X₀).f (essTest c) :=
    (F.map_comp _ _).trans (comp_hom_eq_of_eq_comp_inv _ _ (F.mapIso (integerNormIso _))
      (schemeSpaceMap_ampleModelHom (picardAmple_essObject hc c)))
  exact yoneda.map_injective (congrArg (fun k => k.hom) (h1.trans h2.symm))

variable (hc) in
/-- The comparison of total spaces is an isomorphism. -/
def essTotalIso : ampleModel (picardAmple_essObject hc c) ≅ essTotal c :=
  yoneda.preimageIso ((ampleModelIso (picardAmple_essObject hc c)) ≪≫
    (ObjectProperty.ι _).mapIso (essIso c).symm)

/-- The comparison of total spaces is an isomorphism. -/
instance : IsIso (essTotalMap hc c) :=
  (essTotalIso hc c).isIso_hom

/-- The comparison of total spaces is an isomorphism of underlying schemes. -/
instance : IsIso (SmallEtale.schemeHom (associatedBigEtaleSite B) (essTotalMap hc c).left) :=
  Functor.map_isIso (BigFppfOver.toScheme B integerBase B.contains_integerBase) (essTotalMap hc c)

variable (hc) in
/-- The square of total spaces over the identity of the base is cartesian. -/
theorem isPullback_essTotalMap :
    IsPullback (SmallEtale.schemeHom (associatedBigEtaleSite B) (essTotalMap hc c).left)
      (B.inclusion.map (ampleModelHom (picardAmple_essObject hc c)).left) c.left.toBase
      (B.inclusion.map (𝟙 c.left.base)) :=
  @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ inferInstance
    (Functor.map_isIso B.inclusion (𝟙 c.left.base)) ⟨(congrArg (BigFppfOver.toScheme B integerBase
    B.contains_integerBase).map (essTotalMap_comp_structureMap hc c)).trans
      ((BigFppfOver.toScheme B integerBase B.contains_integerBase).map_comp _ _)⟩

variable (hc) in
/-- The comparison of the modules on the represented algebraic space of the scheme model. -/
def essModuleComparison :
    (Space.modulePullback B integerBase B.contains_integerBase
        (Space.representedSpaceMap B integerBase B.contains_integerBase (essTotalMap hc c))).obj
        (essModule c) ≅ ampleModelModule (picardAmple_essObject hc c) :=
  Space.QuasiCoherentDescent.pullbackComparison B integerBase B.contains_integerBase
    (ampleModelSpaceIso (picardAmple_essObject hc c)).hom (essIso c).inv _
    (schemeSpaceMap_essTotalMap hc c).symm (essModule c)

variable (hc) in
/-- The comparison of polarizations of the scheme model with the given polarization. -/
def essLineBundleIso :
    (Scheme.Modules.pullback (SmallEtale.schemeHom (associatedBigEtaleSite B)
        (essTotalMap hc c).left)).obj c.left.lineBundle ≅
      ampleModelLineBundle (picardAmple_essObject hc c) :=
  (Scheme.Modules.pullback (SmallEtale.schemeHom (associatedBigEtaleSite B)
      (essTotalMap hc c).left)).mapIso (essModuleZariskiIso c).symm ≪≫
    Space.representedZariskiModulePullbackIso B integerBase B.contains_integerBase
      (essTotalMap hc c)
      (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase _)
      (essModule c) (isQuasicoherentOnSite_essModule c) ≪≫
    (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj
          (ampleModel (picardAmple_essObject hc c)))
        (ampleModel (picardAmple_essObject hc c)).left.property).mapIso
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
        (ampleModel (picardAmple_essObject hc c))).inverse.mapIso (essModuleComparison hc c))

variable (hc) in
/-- **The comparison of the polarized family of the object of the Picard stack with the given
family.** -/
def essPolarizedHom : amplePolarizedFamily (picardAmple_essObject hc c) ⟶ c.left where
  baseMap := 𝟙 c.left.base
  totalMap := SmallEtale.schemeHom (associatedBigEtaleSite B) (essTotalMap hc c).left
  cartesian := isPullback_essTotalMap hc c
  lineBundleIso := essLineBundleIso hc c

variable (hc) in
/-- The comparison of polarized families is an isomorphism. -/
theorem isIso_essPolarizedHom : IsIso (essPolarizedHom hc c) := by
  have hbase : IsIso ((polarizedProjection B).map (essPolarizedHom hc c)) :=
    (inferInstance : IsIso (𝟙 c.left.base))
  have : (polarizedProjection B).IsStronglyCartesian
      ((polarizedProjection B).map (essPolarizedHom hc c)) (essPolarizedHom hc c) :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift
      polarizedProjection_isFiberedInGroupoids_unconditional _ (essPolarizedHom hc c)
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso (polarizedProjection B)
    ((polarizedProjection B).map (essPolarizedHom hc c)) (essPolarizedHom hc c)

variable (hc) in
/-- The comparison of polarized families commutes with the two morphisms to `X₀`. -/
theorem essPolarizedHom_comp_hom :
    (forgetPolarization B).map (essPolarizedHom hc c) ≫ c.hom =
      ampleArrow (picardAmple_essObject hc c) := by
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  apply CommaMorphism.ext
  · have e1 : (essIso c).inv ≫ c.hom.hom.hom.left =
        Space.baseChangeProjection (properFlatPicardSituation X₀).f (essTest c) :=
      (Iso.inv_comp_eq _).2 (essIso_hom_baseChangeProjection c).symm
    have h : schemeSpaceMap (essTotalMap hc c) ≫ c.hom.hom.hom.left =
        ampleArrowLeft (picardAmple_essObject hc c) :=
      (congrArg (fun k => k ≫ c.hom.hom.hom.left) (schemeSpaceMap_essTotalMap hc c)).trans
        ((Category.assoc _ _ _).trans (congrArg (fun k =>
          (ampleModelSpaceIso (picardAmple_essObject hc c)).hom ≫ k) e1))
    exact h
  · let F := schemeSpaceFunctor B integerBase B.contains_integerBase
    have e0 : (integerNormIso (essTest c).left).hom = 𝟙 _ :=
      Over.OverMorphism.ext (integerNormIso_hom_left _)
    have e1 : F.map (ampleBaseMap (essObject c)) = F.map c.hom.hom.hom.right :=
      (schemeSpaceMap_ampleBaseMap (essObject c)).trans
        ((congrArg (fun k => F.map k ≫ (essTest c).hom) e0).trans
          ((congrArg (fun k => k ≫ (essTest c).hom) (F.map_id _)).trans (Category.id_comp _)))
    have e2 : F.map ((schemeOverIntegers B).map (𝟙 c.left.base) ≫ c.hom.hom.hom.right) =
        F.map c.hom.hom.hom.right :=
      congrArg F.map ((congrArg (fun k => k ≫ c.hom.hom.hom.right)
        ((schemeOverIntegers B).map_id _)).trans (Category.id_comp _))
    exact yoneda.map_injective (congrArg (fun k => k.hom) (e2.trans e1.symm))

variable (hc) in
/-- **The polarized family over `X₀` of the object of the Picard stack of a polarized family over
`X₀` is that family.** -/
def essIsoCostructuredArrow :
    (amplePolarizedFunctor X₀ hc).obj ⟨essObject c, picardAmple_essObject hc c⟩ ≅ c :=
  CostructuredArrow.isoMk (@asIso _ _ _ _ (essPolarizedHom hc c) (isIso_essPolarizedHom hc c))
    (essPolarizedHom_comp_hom hc c)

/-- **The functor from the relatively ample locus of `Picardstack_{X₀/V₀}` to the polarized
families over `X₀` is essentially surjective.** -/
instance essSurj_amplePolarizedFunctor : (amplePolarizedFunctor X₀ hc).EssSurj where
  mem_essImage c := ⟨⟨essObject c, picardAmple_essObject hc c⟩, ⟨essIsoCostructuredArrow hc c⟩⟩

/-- The functor from the relatively ample locus of `Picardstack_{X₀/V₀}` to the polarized families
over `X₀` is an equivalence. -/
instance isEquivalence_amplePolarizedFunctor : (amplePolarizedFunctor X₀ hc).IsEquivalence where

variable (X₀ hc) in
/-- **The relatively ample locus of `Picardstack_{X₀/V₀}` is equivalent to the category of
polarized families over `X₀`**: the 2-fibre product of `𝒫olarized` with `Spec(V₀)` over
`Spaces'_{fp, flat, proper}`, in the form of the category of objects over `X₀`. -/
def amplePolarizedEquivalence :
    (Space.picardAmple hc (properFlatPicardSituation X₀)).FullSubcategory ≌
      CostructuredArrow (forgetPolarization B) X₀ :=
  (amplePolarizedFunctor X₀ hc).asEquivalence

/-! ### The equivalence lies over the site -/

/-- A morphism of schemes over `Spec(ℤ)` is the morphism of its underlying schemes read over
`Spec(ℤ)`, up to the identifications of the two schemes over `Spec(ℤ)` with their readings. -/
theorem schemeOverIntegers_map_left {V W : BigFppfOver B integerBase B.contains_integerBase}
    (b : V ⟶ W) (hV : (schemeOverIntegers B).obj V.left = V)
    (hW : (schemeOverIntegers B).obj W.left = W) :
    (schemeOverIntegers B).map b.left = eqToHom hV ≫ b ≫ eqToHom hW.symm := by
  apply Over.OverMorphism.ext
  simp
  rfl

variable (X₀ hc) in
/-- **The equivalence between the relatively ample locus of `Picardstack_{X₀/V₀}` and the
polarized families over `X₀` lies over the big fppf site of `Spec(ℤ)`**: an object `(T, L)` lies
over `T`, and so does its polarized family, whose base `T`, read over `Spec(ℤ)` through its unique
structure morphism, is `T` again. -/
theorem amplePolarizedFunctor_comp_projection :
    amplePolarizedFunctor X₀ hc ⋙ CostructuredArrow.proj (forgetPolarization B) X₀ ⋙
        forgetPolarization B ⋙ cartesianProperFlatProjection B integerBase B.contains_integerBase =
      (Space.picardAmple hc (properFlatPicardSituation X₀)).ι ⋙
        (Space.picardCFG hc (properFlatPicardSituation X₀)).val.p := by
  have hobj : ∀ V : BigFppfOver B integerBase B.contains_integerBase,
      (schemeOverIntegers B).obj V.left = V := by
    intro V
    obtain ⟨V, ⟨⟨⟩⟩, h⟩ := V
    change Over.mk _ = Over.mk h
    congr 1
    apply ObjectProperty.hom_ext
    exact specULiftZIsTerminal.hom_ext _ _
  refine CategoryTheory.Functor.ext (fun A => hobj A.obj.T.left) (fun A C m => ?_)
  exact schemeOverIntegers_map_left m.hom.base.left (hobj _) (hobj _)

end AlgebraicGeometry

end
