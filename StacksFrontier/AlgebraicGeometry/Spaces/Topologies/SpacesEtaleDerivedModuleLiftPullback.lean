module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModulePullbackFlatExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleRingedToposHomComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDerivedModuleLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleModulePullbackComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.LocalizedMorphism
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackTopos
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparison
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparisonPullback

/-!
# The derived transport to the spaces-étale site and derived pullback

Let `f : Y ⟶ X` be an étale morphism of algebraic spaces. The derived transport
`ι : D(𝒪_{X_étale}) ⥤ D(𝒪_{X_{spaces,étale}})` of
`AlgebraicGeometry.Space.toSpacesEtaleDerivedModules` commutes with derived pullback along `f`:
on the small étale side `Lf^*` is étale restriction, on the spaces-étale side it is the derived
pullback of Stacks 06YY along the morphism of spaces-étale ringed topoi of Stacks 0DE7, and
on modules the two pullbacks are intertwined by `ι`
(`AlgebraicGeometry.BigEtaleSpaceSite.toSpacesEtaleModulesPullbackHom`).

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.spacesEtalePullbackModulesIsoPullbackTopos`: the pullback
  of modules along the spaces-étale ringed topos morphism of `f` is the pullback along the
  site-presented morphism `f_{small}`.
* `AlgebraicGeometry.BigEtaleSpaceSite.etaleModulePullbackCompToSpacesEtaleModulesIso`:
  `ι(f^*M) ≅ f^*(ιM)` for `f` étale.
* `smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso`:
  `ι(Lf^*K) ≅ Lf^*(ιK)` for `f` étale.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.BigEtaleSpaceSite

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance low] HasDerivedCategory.standard
attribute [local instance 5000] Space.SmallEtale.instHasSheafify
  Space.SmallEtale.instWEqualsLocallyBijective
attribute [local instance] Space.etaleModulePullback_additive
  Space.preservesFiniteLimits_etaleModulePullback Space.preservesFiniteColimits_etaleModulePullback

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) {X Y : T.Spaces} (f : Y ⟶ X)

open Space.SimplicialSpacesEtaleSite Stacks.Cohomology.DerivedPullbackOfToposHom

/-- The pullback of modules along the morphism of spaces-étale ringed topoi of `f`, built from
the adjoint pair of the geometric morphism, is the pullback along the site-presented morphism
`f_{small}`. -/
def spacesEtalePullbackModulesIsoPullbackTopos :
    (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules ≅
      (smallEtaleRingedSiteHom T f).pullbackTopos :=
  eqToIso (RingedToposHom.pullbackModules_eq_pullbackModules_toRingedToposModulesHom
      (spacesEtaleRingedToposHom f)) ≪≫
    (RingedSite.Hom.ofRingedToposSiteHom (smallEtaleRingedSiteHom T f)
      (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f)).pullbackModulesToposIso

/-- **Étale restriction commutes with `ι`**: for `f` étale, restricting an `𝒪_X`-module of the
small étale site along `f` and transporting it to the spaces-étale site of `Y` is pulling back
its transport along the morphism of spaces-étale ringed topoi of `f`. -/
def etaleModulePullbackCompToSpacesEtaleModulesIso
    (hf : Space.IsEtale T.fppfSite S T.fppf_mem f.hom) :
    Space.etaleModulePullback.{u, u} T.fppfSite S T.fppf_mem f hf ⋙
        Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem Y ≅
      Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem X ⋙
        (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules :=
  Functor.isoWhiskerRight
      (Space.modulePullbackIsoEtaleModulePullback T.fppfSite S T.fppf_mem f hf).symm _ ≪≫
    (asIso (toSpacesEtaleModulesPullbackHom T f)).symm ≪≫
    Functor.isoWhiskerLeft _ (spacesEtalePullbackModulesIsoPullbackTopos T f).symm

/-- **The derived transport to the spaces-étale site commutes with derived pullback along étale
morphisms**: for `f : Y ⟶ X` étale, `ι(Lf^*K) ≅ Lf_{spaces,étale}^*(ιK)`, naturally in
`K ∈ D(𝒪_{X_étale})`. -/
def smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso
    (hf : Space.IsEtale T.fppfSite S T.fppf_mem f.hom) :
    Space.smallEtaleDerivedModulePullback T.fppfSite S T.fppf_mem f ⋙
        Space.toSpacesEtaleDerivedModules T.fppfSite S T.fppf_mem Y ≅
      Space.toSpacesEtaleDerivedModules T.fppfSite S T.fppf_mem X ⋙
        derivedPullback (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
          (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
          (spacesEtaleRingedToposHom f) :=
  letI := Space.spacesEtaleHasDerivedCategory T.fppfSite S T.fppf_mem X
  letI := Space.spacesEtaleHasDerivedCategory T.fppfSite S T.fppf_mem Y
  haveI : (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules.Additive :=
    Stacks.Sheaves.DerivedPullback.pullbackModules_additive
      (spacesEtaleRingedToposHom f).toModulesHom
  haveI := open Space in
  preservesFiniteLimits_spacesEtaleRingedToposHom_pullbackModules_spacesEtaleModulePullbackFlatExact
    f (Space.isFlat_of_isEtale T.fppfSite S T.fppf_mem hf)
  haveI : PreservesFiniteColimits (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules :=
    Stacks.Sheaves.DerivedPullback.pullbackModules_preservesFiniteColimits
      (spacesEtaleRingedToposHom f).toModulesHom
  Functor.isoWhiskerRight
      (Space.smallEtaleDerivedModulePullbackIsoEtale T.fppfSite S T.fppf_mem f hf) _ ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (Space.etaleModulePullback.{u, u} T.fppfSite S T.fppf_mem f hf)
      (Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem Y)).symm ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (etaleModulePullbackCompToSpacesEtaleModulesIso T f hf) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem X)
      (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules ≪≫
    Functor.isoWhiskerLeft _
      (Stacks.Homology.leftDerivedIsoMapDerivedCategory _
        (derivedPullback (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
          (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
          (spacesEtaleRingedToposHom f))
        (derivedPullbackComparison (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
          (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
          (spacesEtaleRingedToposHom f))).symm

end AlgebraicGeometry.BigEtaleSpaceSite

end
