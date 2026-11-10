module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategorySquareComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackEtaleComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDerivedModuleLiftPullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtalePullbackToposComp
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# The derived transport to the spaces-étale site commutes with derived pullback, compatibly with
composition

For étale morphisms `g : Z ⟶ Y` and `f : Y ⟶ X` of algebraic spaces, the isomorphisms
`ι(Lf^*K) ≅ Lf^*(ιK)` of `smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso` carry
the composition isomorphism `Lf^* ⋙ Lg^* ≅ L(g ≫ f)^*` of Stacks 0D6D on the small étale sites to
the one on the spaces-étale sites.

## Main results

* `smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_comp`: the transport
  isomorphisms are compatible with the composition isomorphisms of derived pullback.

## Implementation notes

The derived categories of modules on the spaces-étale sites are taken at the standard model
`AlgebraicGeometry.Space.spacesEtaleHasDerivedCategory`, passed explicitly. On the small étale
sites no global `HasDerivedCategory` instance applies, and the standard model is a low-priority
local instance.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.BigEtaleSpaceSite

attribute [local instance 5000] SheafOfModules.instAbelian
-- No global `HasDerivedCategory` instance applies to modules on the small étale sites; at low
-- priority the standard model chooses nothing where a global one exists.
attribute [local instance low] HasDerivedCategory.standard
attribute [local instance 5000] Space.SmallEtale.instHasSheafify
  Space.SmallEtale.instWEqualsLocallyBijective
attribute [local instance] Space.etaleModulePullback_additive
  Space.preservesFiniteLimits_etaleModulePullback Space.preservesFiniteColimits_etaleModulePullback

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) {X Y Z : T.Spaces} (f : Y ⟶ X) (g : Z ⟶ Y)

open Space.SimplicialSpacesEtaleSite Stacks.Cohomology.DerivedPullbackOfToposHom

open AlgebraicGeometry.Space renaming
  preservesFiniteLimits_spacesEtaleRingedToposHom_pullbackModules_spacesEtaleModulePullbackFlatExact
  → preservesFiniteLimits_pullbackModules_of_isFlat

/-- The isomorphism `ι(Lf^*K) ≅ Lf^*(ιK)` in layers: the identification of `Lf^*` with étale
restriction, the square of exact functors induced by
`AlgebraicGeometry.BigEtaleSpaceSite.etaleModulePullbackCompToSpacesEtaleModulesIso`, and the
identification of the spaces-étale `Lf^*` with the functor induced by the exact pullback. -/
theorem smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_eq
    (hf : Space.IsEtale T.fppfSite S T.fppf_mem f.hom) :
    letI := Space.spacesEtaleHasDerivedCategory T.fppfSite S T.fppf_mem X
    letI := Space.spacesEtaleHasDerivedCategory T.fppfSite S T.fppf_mem Y
    haveI : (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules.Additive :=
      Stacks.Sheaves.DerivedPullback.pullbackModules_additive
        (spacesEtaleRingedToposHom f).toModulesHom
    haveI := preservesFiniteLimits_pullbackModules_of_isFlat f
      (Space.isFlat_of_isEtale T.fppfSite S T.fppf_mem hf)
    haveI : PreservesFiniteColimits (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules :=
      Stacks.Sheaves.DerivedPullback.pullbackModules_preservesFiniteColimits
        (spacesEtaleRingedToposHom f).toModulesHom
    smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T f hf =
      Functor.isoWhiskerRight
          (Space.smallEtaleDerivedModulePullbackIsoEtale T.fppfSite S T.fppf_mem f hf)
          (Space.toSpacesEtaleDerivedModules T.fppfSite S T.fppf_mem Y) ≪≫
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
          (Space.etaleModulePullback.{u, u} T.fppfSite S T.fppf_mem f hf)
          (Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem Y)).symm ≪≫
        Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
          (etaleModulePullbackCompToSpacesEtaleModulesIso T f hf) ≪≫
        Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
          (Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem X)
          (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules ≪≫
        Functor.isoWhiskerLeft (Space.toSpacesEtaleDerivedModules T.fppfSite S T.fppf_mem X)
          (Stacks.Homology.leftDerivedIsoMapDerivedCategory _
            (derivedPullback (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
              (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
              (spacesEtaleRingedToposHom f))
            (derivedPullbackComparison (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
              (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
              (spacesEtaleRingedToposHom f))).symm :=
  rfl

/-- **The derived transport to the spaces-étale site commutes with derived pullback along étale
morphisms, compatibly with composition.** For étale `g : Z ⟶ Y` and `f : Y ⟶ X`, `ι` of the
composition isomorphism `Lf^* ⋙ Lg^* ≅ L(g ≫ f)^*` on the small étale sites, followed by
`ι(L(g ≫ f)^*K) ≅ L(g ≫ f)^*(ιK)`, is
`ι(Lg^*Lf^*K) ≅ Lg^*(ι(Lf^*K)) ≅ Lg^*Lf^*(ιK)` followed by the composition isomorphism on the
spaces-étale sites. -/
theorem smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_comp
    (hf : Space.IsEtale T.fppfSite S T.fppf_mem f.hom)
    (hg : Space.IsEtale T.fppfSite S T.fppf_mem g.hom)
    (hgf : Space.IsEtale T.fppfSite S T.fppf_mem (g ≫ f).hom)
    (K : DerivedCategory (Space.Modules.{u, u} T.fppfSite S T.fppf_mem X.1 X.2)) :
    letI := Space.spacesEtaleHasDerivedCategory T.fppfSite S T.fppf_mem X
    letI := Space.spacesEtaleHasDerivedCategory T.fppfSite S T.fppf_mem Y
    letI := Space.spacesEtaleHasDerivedCategory T.fppfSite S T.fppf_mem Z
    (Space.toSpacesEtaleDerivedModules T.fppfSite S T.fppf_mem Z).map
        ((Space.smallEtaleDerivedModulePullbackCompIso T.fppfSite S T.fppf_mem g f).hom.app K) ≫
      (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T (g ≫ f) hgf).hom.app K =
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T g hg).hom.app
        ((Space.smallEtaleDerivedModulePullback T.fppfSite S T.fppf_mem f).obj K) ≫
      (derivedPullback (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z)
          (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
          (spacesEtaleRingedToposHom g)).map
        ((smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T f hf).hom.app K) ≫
      (Space.spacesEtaleDerivedPullbackCompIsoSpacesEtaleRingedToposHomComp g f).hom.app
        ((Space.toSpacesEtaleDerivedModules T.fppfSite S T.fppf_mem X).obj K) := by
  let := Space.spacesEtaleHasDerivedCategory T.fppfSite S T.fppf_mem X
  let := Space.spacesEtaleHasDerivedCategory T.fppfSite S T.fppf_mem Y
  let := Space.spacesEtaleHasDerivedCategory T.fppfSite S T.fppf_mem Z
  have hf' := Space.isFlat_of_isEtale T.fppfSite S T.fppf_mem hf
  have hg' := Space.isFlat_of_isEtale T.fppfSite S T.fppf_mem hg
  have hgf' := Space.isFlat_of_isEtale T.fppfSite S T.fppf_mem hgf
  have : (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules.Additive :=
    Stacks.Sheaves.DerivedPullback.pullbackModules_additive
      (spacesEtaleRingedToposHom f).toModulesHom
  have : (spacesEtaleRingedToposHom g).toModulesHom.pullbackModules.Additive :=
    Stacks.Sheaves.DerivedPullback.pullbackModules_additive
      (spacesEtaleRingedToposHom g).toModulesHom
  have : (spacesEtaleRingedToposHom (g ≫ f)).toModulesHom.pullbackModules.Additive :=
    Stacks.Sheaves.DerivedPullback.pullbackModules_additive
      (spacesEtaleRingedToposHom (g ≫ f)).toModulesHom
  have := preservesFiniteLimits_pullbackModules_of_isFlat f hf'
  have := preservesFiniteLimits_pullbackModules_of_isFlat g hg'
  have := preservesFiniteLimits_pullbackModules_of_isFlat (g ≫ f) hgf'
  have : PreservesFiniteColimits (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules :=
    Stacks.Sheaves.DerivedPullback.pullbackModules_preservesFiniteColimits
      (spacesEtaleRingedToposHom f).toModulesHom
  have : PreservesFiniteColimits (spacesEtaleRingedToposHom g).toModulesHom.pullbackModules :=
    Stacks.Sheaves.DerivedPullback.pullbackModules_preservesFiniteColimits
      (spacesEtaleRingedToposHom g).toModulesHom
  have : PreservesFiniteColimits
      (spacesEtaleRingedToposHom (g ≫ f)).toModulesHom.pullbackModules :=
    Stacks.Sheaves.DerivedPullback.pullbackModules_preservesFiniteColimits
      (spacesEtaleRingedToposHom (g ≫ f)).toModulesHom
  have hP3 := Space.smallEtaleDerivedModulePullbackCompIso_hom_comp_isoEtale g f hg hf hgf
  have hP1 := Stacks.DerivedCategoryComparisons.mapDerivedCategorySquareIso_comp_hom
    (Space.etaleModulePullback.{u, u} T.fppfSite S T.fppf_mem f hf)
    (Space.etaleModulePullback.{u, u} T.fppfSite S T.fppf_mem g hg)
    (Space.etaleModulePullback.{u, u} T.fppfSite S T.fppf_mem (g ≫ f) hgf)
    (Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem X)
    (Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem Y)
    (Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem Z)
    (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules
    (spacesEtaleRingedToposHom g).toModulesHom.pullbackModules
    (spacesEtaleRingedToposHom (g ≫ f)).toModulesHom.pullbackModules
    (etaleModulePullbackCompToSpacesEtaleModulesIso T f hf)
    (etaleModulePullbackCompToSpacesEtaleModulesIso T g hg)
    (etaleModulePullbackCompToSpacesEtaleModulesIso T (g ≫ f) hgf)
    (Space.etaleModulePullbackComp T.fppfSite S T.fppf_mem g f hg hf hgf)
    ((RingedToposHom.pullbackModulesCompIso (spacesEtaleRingedToposHom g)
      (spacesEtaleRingedToposHom f)).symm ≪≫
        Space.spacesEtalePullbackModulesCompIsoSpacesEtaleRingedToposHomComp g f)
    (etaleModulePullbackCompToSpacesEtaleModulesIso_comp T f g hf hg hgf)
  have hP2 := spacesEtaleDerivedPullbackCompIso_hom_comp_leftDerivedIsoMapDerivedCategory T f g
    hf' hg' hgf'
  simp only [Stacks.DerivedCategoryComparisons.mapDerivedCategorySquareIso] at hP1
  exact Stacks.CategoryTheory.squareIso_pasting_of_layers_of_eq
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T f hf)
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T g hg)
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso T (g ≫ f) hgf)
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_eq T f hf)
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_eq T g hg)
    (smallEtaleDerivedModulePullbackCompToSpacesEtaleDerivedModulesIso_eq T (g ≫ f) hgf)
    _ _ _ _ hP3 hP1 hP2 K

end AlgebraicGeometry.BigEtaleSpaceSite

end
