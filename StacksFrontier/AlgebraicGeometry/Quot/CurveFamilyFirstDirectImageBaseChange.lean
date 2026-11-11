module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyBaseChangeFieldFibre
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomologyDerived
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliCurves
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatDerivedPushforwardDegreeOne
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStructureSheafPushforward

/-!
# `R¹f_*𝒪_X` of a family of curves: finite local freeness and base change

Let `f : X → S` be a family of curves (Stacks 0D4Z) such that `k = H⁰(X_k, 𝒪_{X_k})` for every
morphism `Spec k → S` from the spectrum of a field. Then the first higher direct image
`R¹f_*𝒪_X` (`AlgebraicGeometry.CurveFamily.firstDirectImage`) is a finite locally free
`𝒪_S`-module, and its formation commutes with arbitrary base change: for every morphism of
families `X' → X` over `h : S' → S`, the base change map `h^*(R¹f_*𝒪_X) ⟶ R¹f'_*𝒪_{X'}` is an
isomorphism. These are parts (2) and (3)
of Stacks 0E1J.

This holds in particular when `f_*𝒪_X = 𝒪_S` universally
(`AlgebraicGeometry.HasUniversallyBijectiveGlobalFunctions`), so for prestable and stable families
and for the families of `Curves^{smooth, h0}`, and when the geometric fibres of `f` are reduced
and connected (the condition of `Curves^{grc}`, through Stacks 0E0S).

## Main results

* `CurveFamily.isFiniteLocallyFreeOnSite_firstDirectImage_of_bijective_algebraMap_fibre`.
* `CurveFamily.firstDirectImageBaseChangeMap`: the base change map
  `h^*R¹f_*𝒪_X ⟶ R¹f'_*𝒪_{X'}` of a morphism of families.
* `CurveFamily.isIso_firstDirectImageBaseChangeMap_of_bijective_algebraMap_fibre`: it is an
  isomorphism.
* `CurveFamily.nonempty_modulePullback_firstDirectImage_iso_of_bijective_algebraMap_fibre`.
* the same under `HasUniversallyBijectiveGlobalFunctions`, for prestable, stable and smooth `h0`
  families, and for families with geometrically reduced and connected fibres.

## References

* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 0E0S](https://stacks.math.columbia.edu/tag/0E0S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

-- global `HasDerivedCategory` instances in scope here (`Homology/DerivedCategory/LocallySmall` and
-- others) compete with the standard model in which the derived functors used here are stated
attribute [-instance] AlgebraicGeometry.RingedSpace.hasDerivedCategoryOXMod
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory
  AlgebraicGeometry.SmallEtale.hasDerivedCategory_smallEtaleRingedSite
  Stacks.DerivedQCoh.hasDerivedCategoryQuasicoherent

namespace AlgebraicGeometry

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

attribute [local instance] Space.hasInjectiveResolutions_modules Space.enoughInjectives_modules in
/-- The cohomology of the structure sheaf of a fibre of a family of curves over a field vanishes
above degree `1`, the fibre taken along `ObjectProperty.homMk (yonedaEquiv.symm p.value)`. -/
theorem isZero_rightDerived_globalSectionsFunctor_structureSheafModule_fiberProduct
    (X : CurveFamily B hZ) (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    (j : ℕ) (hj : 2 ≤ j) :
    IsZero (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B integerBase hZ
        (AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase
          (ObjectProperty.homMk (yonedaEquiv.symm p.value) :
            schemeSpace p.siteObject ⟶ schemeSpace X.base)).1
        (AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase
          (ObjectProperty.homMk (yonedaEquiv.symm p.value) :
            schemeSpace p.siteObject ⟶ schemeSpace X.base)).2).O)).rightDerived j).obj
      (Space.structureSheafModule B integerBase hZ (AlgebraicSpaces.fiberProduct B integerBase hZ
        X.toBase (ObjectProperty.homMk (yonedaEquiv.symm p.value) :
          schemeSpace p.siteObject ⟶ schemeSpace X.base)))) := by
  have hg : (ObjectProperty.homMk (yonedaEquiv.symm p.value) :
      schemeSpace p.siteObject ⟶ schemeSpace X.base) = schemeSpaceMap p.value := by
    exact InducedCategory.hom_ext <| yonedaEquiv.injective ((yonedaEquiv.apply_symm_apply _).trans
      (yonedaEquiv_yoneda_map p.value).symm)
  rw [hg]
  exact X.isZero_rightDerived_globalSectionsFunctor_fiberProduct_fieldValuedPoint p _
    (SheafOfModules.isQuasicoherentOnSite_unit _) hj

/-- **`R¹f_*𝒪_X` is finite locally free (Stacks 0E1J (2))**, for a family of curves with
`k = H⁰(X_k, 𝒪_{X_k})` on every fibre over a field. -/
theorem isFiniteLocallyFreeOnSite_firstDirectImage_of_bijective_algebraMap_fibre
    (X : CurveFamily B hZ)
    (h : ∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj,
      Function.Bijective (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier))
        p.contained (Space.fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom p)))) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (X.firstDirectImage B hZ) :=
  SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
    X.homologyDerivedPushforwardIsoFirstHigherDirectImage
    (Space.isFiniteLocallyFreeOnSite_homology_one_derivedModulePushforward X.toBase X.proper
      X.flat X.finitePresentation h fun p j hj =>
        X.isZero_rightDerived_globalSectionsFunctor_structureSheafModule_fiberProduct p j hj)

/-- **The formation of `R¹f_*𝒪_X` commutes with arbitrary base change (Stacks 0E1J (3))**, for a
family of curves with `k = H⁰(X_k, 𝒪_{X_k})` on every fibre over a field: for every morphism of
families `a : F ⟶ X`, over `h : S' ⟶ S`, `h^*(R¹f_*𝒪_X) ≅ R¹f'_*𝒪_{X'}`. -/
theorem nonempty_modulePullback_firstDirectImage_iso_of_bijective_algebraMap_fibre
    (X : CurveFamily B hZ)
    (h : ∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj,
      Function.Bijective (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier))
        p.contained (Space.fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom p))))
    (F : CurveFamily B hZ) (a : F ⟶ X) :
    Nonempty ((Space.modulePullback B integerBase hZ (schemeSpaceMap a.baseMap)).obj
        (X.firstDirectImage B hZ) ≅ F.firstDirectImage B hZ) := by
  obtain ⟨e⟩ := Space.nonempty_modulePullback_homology_one_derivedModulePushforward_iso X.toBase
    X.proper X.flat X.finitePresentation h
    (fun p j hj =>
      X.isZero_rightDerived_globalSectionsFunctor_structureSheafModule_fiberProduct p j hj)
    (schemeSpaceMap a.baseMap) F.toBase a.totalMap a.cartesian
  exact ⟨(Space.modulePullback B integerBase hZ (schemeSpaceMap a.baseMap)).mapIso
      X.homologyDerivedPushforwardIsoFirstHigherDirectImage.symm ≪≫ e ≪≫
    F.homologyDerivedPushforwardIsoFirstHigherDirectImage⟩

/-! ### The base change map of `R¹f_*𝒪_X` -/

/-- **The base change map of `R¹f_*𝒪_X`** along a morphism of families of curves `a : F ⟶ X`
over `h : S' ⟶ S`, with `f' : X' → S'` the base change of `f : X → S`: the canonical map
`h^*R¹f_*𝒪_X ⟶ R¹f'_*𝒪_{X'}`. It is
`h^*R¹f_*𝒪_X = h^*H¹(Rf_*𝒪_X) ⟶ H¹(Lh^*Rf_*𝒪_X)`, then `H¹` of the base change map
`Lh^*Rf_*𝒪_X ⟶ Rf'_*L(h')^*𝒪_X` of the cartesian square of `a` (Stacks 07A7), then
`H¹(Rf'_*L(h')^*𝒪_X) = H¹(Rf'_*𝒪_{X'}) = R¹f'_*𝒪_{X'}`. -/
def firstDirectImageBaseChangeMap {X F : CurveFamily B hZ} (a : F ⟶ X) :
    (Space.modulePullback B integerBase hZ (schemeSpaceMap a.baseMap)).obj
        (X.firstDirectImage B hZ) ⟶ F.firstDirectImage B hZ :=
  (Space.modulePullback B integerBase hZ (schemeSpaceMap a.baseMap)).map
      X.homologyDerivedPushforwardIsoFirstHigherDirectImage.inv ≫
    Space.modulePullbackHomologyDerivedModulePushforwardBaseChangeMap X.toBase
      (schemeSpaceMap a.baseMap) F.toBase a.totalMap a.cartesian.w
      ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)) 1 ≫
    (DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Space.ringedToposStructureRingSheaf B integerBase hZ (schemeSpace F.base))) 1).map
      ((Space.derivedModulePushforward B integerBase hZ F.toBase).map
        (Space.smallEtaleDerivedModulePullbackUnitIso a.totalMap).hom) ≫
    F.homologyDerivedPushforwardIsoFirstHigherDirectImage.hom

/-- **The base change map of `R¹f_*𝒪_X` is an isomorphism (Stacks 0E1J (3))**, for a family of
curves with `k = H⁰(X_k, 𝒪_{X_k})` on every fibre over a field: for every morphism of families
`a : F ⟶ X` over `h : S' ⟶ S`, the canonical map `h^*R¹f_*𝒪_X ⟶ R¹f'_*𝒪_{X'}` is an
isomorphism. -/
theorem isIso_firstDirectImageBaseChangeMap_of_bijective_algebraMap_fibre
    (X : CurveFamily B hZ)
    (h : ∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj,
      Function.Bijective (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier))
        p.contained (Space.fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom p))))
    (F : CurveFamily B hZ) (a : F ⟶ X) :
    IsIso (firstDirectImageBaseChangeMap a) := by
  have := Space.isIso_modulePullbackHomologyDerivedModulePushforwardBaseChangeMap_one X.toBase
    X.proper X.flat X.finitePresentation h
    (fun p j hj =>
      X.isZero_rightDerived_globalSectionsFunctor_structureSheafModule_fiberProduct p j hj)
    (schemeSpaceMap a.baseMap) F.toBase a.totalMap a.cartesian
  rw [firstDirectImageBaseChangeMap]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' this (IsIso.comp_isIso'
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Space.ringedToposStructureRingSheaf B integerBase hZ (schemeSpace F.base))) 1).mapIso
      ((Space.derivedModulePushforward B integerBase hZ F.toBase).mapIso
        (Space.smallEtaleDerivedModulePullbackUnitIso a.totalMap))).isIso_hom
    (Iso.isIso_hom _)))

/-! ### Families with `f_*𝒪_X = 𝒪_S` universally, and with reduced connected geometric fibres -/

/-- `f_*𝒪_X = 𝒪_S` universally gives `k = H⁰(X_k, 𝒪_{X_k})` on the fibres over fields, formed
over the field. -/
theorem bijective_algebraMap_fibre_of_hasUniversallyBijectiveGlobalFunctions
    {X : CurveFamily B hZ} (hX : HasUniversallyBijectiveGlobalFunctions B hZ X)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) :
    Function.Bijective (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier))
      p.contained (Space.fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom p))) :=
  (Space.bijective_algebraMap_fibreOverFieldValuedPoint_iff B integerBase hZ X.toBase.hom p
    X.total.2 (schemeSpace X.base).2).2
    (hX (schemeSpace p.siteObject) (ObjectProperty.homMk (yonedaEquiv.symm p.value)))

/-- **`R¹f_*𝒪_X` is finite locally free** for a family of curves with `f_*𝒪_X = 𝒪_S` universally
— a prestable, stable or smooth `h0` family. -/
theorem isFiniteLocallyFreeOnSite_firstDirectImage_of_hasUniversallyBijectiveGlobalFunctions
    {X : CurveFamily B hZ} (hX : HasUniversallyBijectiveGlobalFunctions B hZ X) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (X.firstDirectImage B hZ) :=
  X.isFiniteLocallyFreeOnSite_firstDirectImage_of_bijective_algebraMap_fibre
    (bijective_algebraMap_fibre_of_hasUniversallyBijectiveGlobalFunctions hX)

/-- **The formation of `R¹f_*𝒪_X` commutes with arbitrary base change** for a family of curves
with `f_*𝒪_X = 𝒪_S` universally — a prestable, stable or smooth `h0` family. -/
theorem nonempty_modulePullback_firstDirectImage_iso_of_hasUniversallyBijectiveGlobalFunctions
    {X : CurveFamily B hZ} (hX : HasUniversallyBijectiveGlobalFunctions B hZ X)
    (F : CurveFamily B hZ) (a : F ⟶ X) :
    Nonempty ((Space.modulePullback B integerBase hZ (schemeSpaceMap a.baseMap)).obj
        (X.firstDirectImage B hZ) ≅ F.firstDirectImage B hZ) :=
  X.nonempty_modulePullback_firstDirectImage_iso_of_bijective_algebraMap_fibre
    (bijective_algebraMap_fibre_of_hasUniversallyBijectiveGlobalFunctions hX) F a

/-- For a family of curves whose geometric fibres are reduced and connected, `k = H⁰(X_k, 𝒪_{X_k})`
on the fibres over fields (Stacks 0E0S, through Stacks 0DMY (7) for algebraic spaces). -/
theorem bijective_algebraMap_fibre_of_geometricFibres (X : CurveFamily B hZ)
    (hred : ∀ y : Space.GeometricPoint B integerBase hZ (schemeSpace X.base).obj,
      Space.HasEtaleLocalProperty B (Spec (.of y.1.carrier)) y.1.contained
        (Space.fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom y.1)
        (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T))
    (hconn : ∀ y : Space.GeometricPoint B integerBase hZ (schemeSpace X.base).obj,
      Space.ConnectedPoints B (Spec (.of y.1.carrier)) y.1.contained
        (Space.fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom y.1))
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) :
    Function.Bijective (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier))
      p.contained (Space.fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom p))) :=
  Space.bijective_algebraMap_globalFunctions_fibre_of_geometricFibres B integerBase hZ
    X.toBase.hom X.total.2 (schemeSpace X.base).2 hred hconn p _
    (Space.isProper_restrictedFibre B integerBase hZ X.toBase.hom p.contained _ p.value X.total.2
      (schemeSpace X.base).2 X.proper)

end CurveFamily

end AlgebraicGeometry

end
