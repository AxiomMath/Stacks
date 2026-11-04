module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDerivedModuleLiftPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfExactPullbacksCanonical

/-!
# The derived transport to the spaces-étale site, derived pullback, and composition

For flat morphisms `g : Z ⟶ Y` and `f : Y ⟶ X` of algebraic spaces, the composition
isomorphism `L(f ∘ g)^* ≅ Lg^* ∘ Lf^*` of derived pullbacks on the spaces-étale sites is
identified, through the isomorphisms `Lf^* ≅ D(f^*)` with the derived functors of the exact
pullbacks of modules, with the composition isomorphism of those exact pullbacks.

## Main results

* `spacesEtaleDerivedPullbackCompIso_hom_comp_leftDerivedIsoMapDerivedCategory`: on the
  spaces-étale sites, the composition isomorphism of derived pullbacks along flat morphisms is
  the composition isomorphism of the exact pullbacks of modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [-instance] Stacks.ConstantSheaf.hasWeakSheafify_addCommGrp_of_univLE

namespace AlgebraicGeometry.BigEtaleSpaceSite

open Space.SimplicialSpacesEtaleSite Stacks.Cohomology.DerivedPullbackOfToposHom

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) {X Y Z : T.Spaces} (f : Y ⟶ X) (g : Z ⟶ Y)



/-- Instance shortcut on the spaces-étale sites. -/
theorem spacesEtale_hasSheafCompose_forget_ringCat (W : T.Spaces) :
    (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem W).J.HasSheafCompose
      (forget RingCat.{u + 1}) :=
  inferInstance
/-- Instance shortcut on the spaces-étale sites. -/
theorem spacesEtale_hasSheafCompose_forget₂_commRingCat (W : T.Spaces) :
    (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem W).J.HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  inferInstance
/-- Instance shortcut on the spaces-étale sites. -/
theorem spacesEtale_hasSheafCompose_forget_addCommGrpCat (W : T.Spaces) :
    (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem W).J.HasSheafCompose
      (forget AddCommGrpCat.{u + 1}) :=
  inferInstance
/-- Instance shortcut on the spaces-étale sites. -/
theorem spacesEtale_hasSheafify_addCommGrpCat (W : T.Spaces) :
    HasSheafify (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem W).J AddCommGrpCat.{u + 1} :=
  inferInstance
/-- Instance shortcut on the spaces-étale sites. -/
theorem spacesEtale_wEqualsLocallyBijective_addCommGrpCat (W : T.Spaces) :
    (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem W).J.WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  inferInstance
/-- Instance shortcut on the spaces-étale sites. -/
theorem spacesEtale_hasSheafify_type (W : T.Spaces) :
    HasSheafify (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem W).J (Type (u + 1)) :=
  inferInstance

attribute [local instance 30000] spacesEtale_hasSheafCompose_forget_ringCat
  spacesEtale_hasSheafCompose_forget₂_commRingCat spacesEtale_hasSheafCompose_forget_addCommGrpCat
  spacesEtale_hasSheafify_addCommGrpCat spacesEtale_wEqualsLocallyBijective_addCommGrpCat
  spacesEtale_hasSheafify_type

/-- On the spaces-étale sites, derived pullbacks along flat morphisms compose as the exact
pullbacks of modules. -/
theorem spacesEtaleDerivedPullbackCompIso_hom_comp_leftDerivedIsoMapDerivedCategory
    (hf : Space.IsFlat T.fppfSite S T.fppf_mem f.hom)
    (hg : Space.IsFlat T.fppfSite S T.fppf_mem g.hom)
    (hgf : Space.IsFlat T.fppfSite S T.fppf_mem (g ≫ f).hom) :
    letI := Space.spacesEtaleHasDerivedCategory T.fppfSite S T.fppf_mem X
    letI := Space.spacesEtaleHasDerivedCategory T.fppfSite S T.fppf_mem Y
    letI := Space.spacesEtaleHasDerivedCategory T.fppfSite S T.fppf_mem Z
    haveI : (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules.Additive :=
      Stacks.Sheaves.DerivedPullback.pullbackModules_additive
        (spacesEtaleRingedToposHom f).toModulesHom
    haveI : (spacesEtaleRingedToposHom g).toModulesHom.pullbackModules.Additive :=
      Stacks.Sheaves.DerivedPullback.pullbackModules_additive
        (spacesEtaleRingedToposHom g).toModulesHom
    haveI : (spacesEtaleRingedToposHom (g ≫ f)).toModulesHom.pullbackModules.Additive :=
      Stacks.Sheaves.DerivedPullback.pullbackModules_additive
        (spacesEtaleRingedToposHom (g ≫ f)).toModulesHom
    haveI := Space.preservesFiniteLimits_spacesEtaleRingedToposHom_pullbackModules_spacesEtaleModulePullbackFlatExact f hf
    haveI := Space.preservesFiniteLimits_spacesEtaleRingedToposHom_pullbackModules_spacesEtaleModulePullbackFlatExact g hg
    haveI := Space.preservesFiniteLimits_spacesEtaleRingedToposHom_pullbackModules_spacesEtaleModulePullbackFlatExact (g ≫ f) hgf
    haveI : PreservesFiniteColimits (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules :=
      Stacks.Sheaves.DerivedPullback.pullbackModules_preservesFiniteColimits
        (spacesEtaleRingedToposHom f).toModulesHom
    haveI : PreservesFiniteColimits (spacesEtaleRingedToposHom g).toModulesHom.pullbackModules :=
      Stacks.Sheaves.DerivedPullback.pullbackModules_preservesFiniteColimits
        (spacesEtaleRingedToposHom g).toModulesHom
    haveI : PreservesFiniteColimits
        (spacesEtaleRingedToposHom (g ≫ f)).toModulesHom.pullbackModules :=
      Stacks.Sheaves.DerivedPullback.pullbackModules_preservesFiniteColimits
        (spacesEtaleRingedToposHom (g ≫ f)).toModulesHom
    (Space.spacesEtaleDerivedPullbackCompIsoSpacesEtaleRingedToposHomComp g f).hom ≫
        (Stacks.Homology.leftDerivedIsoMapDerivedCategory _
          (derivedPullback (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z)
            (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
            (spacesEtaleRingedToposHom (g ≫ f)))
          (derivedPullbackComparison (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z)
            (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
            (spacesEtaleRingedToposHom (g ≫ f)))).hom =
      Functor.whiskerRight (Stacks.Homology.leftDerivedIsoMapDerivedCategory _
          (derivedPullback (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
            (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
            (spacesEtaleRingedToposHom f))
          (derivedPullbackComparison (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
            (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
            (spacesEtaleRingedToposHom f))).hom
          (derivedPullback (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z)
            (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
            (spacesEtaleRingedToposHom g)) ≫
        Functor.whiskerLeft
          (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules.mapDerivedCategory
          (Stacks.Homology.leftDerivedIsoMapDerivedCategory _
            (derivedPullback (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z)
              (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
              (spacesEtaleRingedToposHom g))
            (derivedPullbackComparison (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z)
              (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
              (spacesEtaleRingedToposHom g))).hom ≫
        (Stacks.Homology.mapDerivedCategoryCompIso
          (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules
          (spacesEtaleRingedToposHom g).toModulesHom.pullbackModules
          (spacesEtaleRingedToposHom (g ≫ f)).toModulesHom.pullbackModules
          ((RingedToposHom.pullbackModulesCompIso (spacesEtaleRingedToposHom g)
            (spacesEtaleRingedToposHom f)).symm ≪≫
            Space.spacesEtalePullbackModulesCompIsoSpacesEtaleRingedToposHomComp g f)).hom := by
  let := Space.spacesEtaleHasDerivedCategory T.fppfSite S T.fppf_mem X
  let := Space.spacesEtaleHasDerivedCategory T.fppfSite S T.fppf_mem Y
  let := Space.spacesEtaleHasDerivedCategory T.fppfSite S T.fppf_mem Z
  have : ∀ {A B : T.Spaces} (h : A ⟶ B),
      (spacesEtaleRingedToposHom h).toModulesHom.pullbackModules.Additive :=
    fun h => Stacks.Sheaves.DerivedPullback.pullbackModules_additive
      (spacesEtaleRingedToposHom h).toModulesHom
  have : ∀ {A B : T.Spaces} (h : A ⟶ B),
      PreservesFiniteColimits (spacesEtaleRingedToposHom h).toModulesHom.pullbackModules :=
    fun h => Stacks.Sheaves.DerivedPullback.pullbackModules_preservesFiniteColimits
      (spacesEtaleRingedToposHom h).toModulesHom
  have := Space.preservesFiniteLimits_spacesEtaleRingedToposHom_pullbackModules_spacesEtaleModulePullbackFlatExact f hf
  have := Space.preservesFiniteLimits_spacesEtaleRingedToposHom_pullbackModules_spacesEtaleModulePullbackFlatExact g hg
  have := Space.preservesFiniteLimits_spacesEtaleRingedToposHom_pullbackModules_spacesEtaleModulePullbackFlatExact (g ≫ f) hgf
  open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom in
  exact derivedPullbackCompIso_hom_comp_leftDerivedIsoMapDerivedCategory
    (spacesEtaleRingedToposHom g) (spacesEtaleRingedToposHom f)
    (Space.spacesEtalePullbackModulesCompIsoSpacesEtaleRingedToposHomComp g f)

end AlgebraicGeometry.BigEtaleSpaceSite

end
