module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategorySquareCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelEtaleDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelEtaleModulesComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelEtaleTransportCoherence
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestrictionNaturality

/-!
# Derived étale pullback on the spaces-étale model and on the small étale site

Let `j : X ⟶ Y` be an étale morphism of algebraic spaces. Under the equivalences
`AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv` of Stacks 03G1, the derived pullback `Lj^*`
along the morphism of models `AlgebraicGeometry.Space.spacesEtaleModelHom j` corresponds to the
functor that the (exact) étale pullback `AlgebraicGeometry.Space.etaleModulePullback j` of
`𝒪`-modules on the small étale sites induces on derived categories.

## Main results

* `AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackOfEtaleTransportIso`:
  `Lj^* ⋙ D(e_X) ≅ D(e_Y) ⋙ D(j^*)`.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance high] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (j : X ⟶ Y) (hj : IsEtale B S hS j.hom)

/-- The étale pullback `j^*` of `𝒪`-modules on the small étale sites, read on the spaces-étale
model of `Y` through the equivalence `AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv` of
Stacks 03G1. -/
abbrev spacesEtaleModelModulesEquivEtalePullback :
    (spacesEtaleModelRingedTopos B S hS Y).Modules ⥤ Modules.{u, u} B S hS X.1 X.2 :=
  (spacesEtaleModelModulesEquiv B S hS Y).functor ⋙ etaleModulePullback.{u, u} B S hS j hj

/-- The functor `AlgebraicGeometry.Space.spacesEtaleModelModulesEquivEtalePullback` is additive. -/
instance spacesEtaleModelModulesEquivEtalePullback_additive :
    (spacesEtaleModelModulesEquivEtalePullback B S hS j hj).Additive :=
  haveI := etaleModulePullback_additive B S hS j hj
  Functor.additive_of_preserves_binary_products _

/-- **The derived pullback along an étale morphism on the spaces-étale models is the derived
étale pullback on the small étale sites**, under the equivalences of Stacks 03G1. -/
def spacesEtaleModelDerivedPullbackOfEtaleTransportIso :
    haveI := etaleModulePullback_additive B S hS j hj
    haveI := preservesFiniteLimits_etaleModulePullback B S hS j hj
    haveI := preservesFiniteColimits_etaleModulePullback B S hS j hj
    derivedPullback (spacesEtaleModelHom B S hS j) ⋙
        (spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory ≅
      (spacesEtaleModelModulesEquiv B S hS Y).functor.mapDerivedCategory ⋙
        (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory :=
  haveI := preservesFiniteLimits_spacesEtaleModelHom_pullbackTopos B S hS j hj
  haveI := etaleModulePullback_additive B S hS j hj
  haveI := preservesFiniteLimits_etaleModulePullback B S hS j hj
  haveI := preservesFiniteColimits_etaleModulePullback B S hS j hj
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS X)).1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS X)).2.1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS X)).2.2
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS Y)).1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS Y)).2.1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS Y)).2.2
  haveI : PreservesFiniteLimits (spacesEtaleModelModulesEquivEtalePullback B S hS j hj) :=
    comp_preservesFiniteLimits _ _
  haveI : PreservesFiniteColimits (spacesEtaleModelModulesEquivEtalePullback B S hS j hj) :=
    comp_preservesFiniteColimits _ _
  haveI : ((spacesEtaleModelHom B S hS j).pullbackTopos ⋙
      (spacesEtaleModelModulesEquiv B S hS X).functor).Additive :=
    Functor.additive_of_preserves_binary_products _
  Functor.isoWhiskerRight (spacesEtaleModelDerivedPullbackIsoOfEtale B S hS j hj) _ ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso
      ((spacesEtaleModelHom B S hS j).pullbackTopos ⋙
        (spacesEtaleModelModulesEquiv B S hS X).functor)
      (spacesEtaleModelModulesEquivEtalePullback B S hS j hj)
      (Functor.isoWhiskerRight (spacesEtaleModelPullbackIsoPushforward B S hS j hj) _ ≪≫
        spacesEtaleModelModulesEquivPostcompIso B S hS j hj) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _

/-- `AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackIsoOfEtale` at the image of an object
of the homotopy category: the comparison `Lj^* ∘ Q ⟶ Q ∘ j^*`, followed by the canonical
factorization of the functor `j^*` induces on derived categories. -/
theorem spacesEtaleModelDerivedPullbackIsoOfEtale_hom_app_Qh
    (J : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS Y).O)) (ComplexShape.up ℤ)) :
    haveI := preservesFiniteLimits_spacesEtaleModelHom_pullbackTopos B S hS j hj
    (spacesEtaleModelDerivedPullbackIsoOfEtale B S hS j hj).hom.app (DerivedCategory.Qh.obj J) =
      (derivedPullbackComparison (spacesEtaleModelHom B S hS j)).app J ≫
        (spacesEtaleModelHom B S hS j).pullbackTopos.mapDerivedCategoryFactorsh.inv.app J := by
  have := preservesFiniteLimits_spacesEtaleModelHom_pullbackTopos B S hS j hj
  dsimp only [spacesEtaleModelDerivedPullbackIsoOfEtale,
    derivedPullbackIsoMapDerivedCategoryOfExact]
  rw [← Stacks.Homology.leftDerivedIsoMapDerivedCategory_hom_app, Category.assoc,
    Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

section Comp

variable {Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsEtale B S hS f.hom)
  (hg : IsEtale B S hS g.hom) (hfg : IsEtale B S hS (f ≫ g).hom)

/-- **The composition isomorphism of derived pullbacks along étale morphisms of models is the
derived composition isomorphism of the inverse images**: through the identifications
`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackIsoOfEtale` of `Lj^*` with the functor
`j^*` induces on derived categories, `Lf^* ∘ Lg^* ≅ L(f ≫ g)^*` is the comparison induced by
`AlgebraicGeometry.Space.spacesEtaleModelPullbackComp`. -/
theorem spacesEtaleModelDerivedPullbackCompIso_hom_app_comp_isoOfEtale
    (K : DerivedCategory (spacesEtaleModelRingedTopos B S hS Z).Modules) :
    haveI := preservesFiniteLimits_spacesEtaleModelHom_pullbackTopos B S hS f hf
    haveI := preservesFiniteLimits_spacesEtaleModelHom_pullbackTopos B S hS g hg
    haveI := preservesFiniteLimits_spacesEtaleModelHom_pullbackTopos B S hS (f ≫ g) hfg
    (spacesEtaleModelDerivedPullbackCompIso B S hS f g).hom.app K ≫
        (spacesEtaleModelDerivedPullbackIsoOfEtale B S hS (f ≫ g) hfg).hom.app K =
      (derivedPullback (spacesEtaleModelHom B S hS f)).map
          ((spacesEtaleModelDerivedPullbackIsoOfEtale B S hS g hg).hom.app K) ≫
        (spacesEtaleModelDerivedPullbackIsoOfEtale B S hS f hf).hom.app
          ((spacesEtaleModelHom B S hS g).pullbackTopos.mapDerivedCategory.obj K) ≫
        (Functor.mapDerivedCategoryCompIsoOfCompIso
          (spacesEtaleModelPullbackComp B S hS f g)).hom.app K := by
  have := preservesFiniteLimits_spacesEtaleModelHom_pullbackTopos B S hS f hf
  have := preservesFiniteLimits_spacesEtaleModelHom_pullbackTopos B S hS g hg
  have := preservesFiniteLimits_spacesEtaleModelHom_pullbackTopos B S hS (f ≫ g) hfg
  have key : (spacesEtaleModelDerivedPullbackCompIso B S hS f g).hom ≫
        (spacesEtaleModelDerivedPullbackIsoOfEtale B S hS (f ≫ g) hfg).hom =
      Functor.whiskerRight (spacesEtaleModelDerivedPullbackIsoOfEtale B S hS g hg).hom
          (derivedPullback (spacesEtaleModelHom B S hS f)) ≫
        Functor.whiskerLeft (spacesEtaleModelHom B S hS g).pullbackTopos.mapDerivedCategory
          (spacesEtaleModelDerivedPullbackIsoOfEtale B S hS f hf).hom ≫
        (Functor.mapDerivedCategoryCompIsoOfCompIso
          (spacesEtaleModelPullbackComp B S hS f g)).hom := by
    refine Localization.natTrans_ext DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) fun J => ?_
    have n := (spacesEtaleModelDerivedPullbackIsoOfEtale B S hS f hf).hom.naturality
      ((spacesEtaleModelHom B S hS g).pullbackTopos.mapDerivedCategoryFactorsh.hom.app J)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    rw [spacesEtaleModelDerivedPullbackIsoOfEtale_hom_app_Qh B S hS (f ≫ g) hfg J,
      reassoc_of% (spacesEtaleModelDerivedPullbackCompIso_hom_app_comp_derivedPullbackComparison_app
        B S hS f g J),
      Functor.mapDerivedCategoryCompIso_hom_app_Qh,
      spacesEtaleModelDerivedPullbackIsoOfEtale_hom_app_Qh B S hS g hg J, ← reassoc_of% n,
      spacesEtaleModelDerivedPullbackIsoOfEtale_hom_app_Qh B S hS f hf]
    have c : (derivedPullback (spacesEtaleModelHom B S hS f)).map
          ((spacesEtaleModelHom B S hS g).pullbackTopos.mapDerivedCategoryFactorsh.inv.app J) ≫
        (derivedPullback (spacesEtaleModelHom B S hS f)).map
          ((spacesEtaleModelHom B S hS g).pullbackTopos.mapDerivedCategoryFactorsh.hom.app J) =
        𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [reassoc_of% c]
  exact congrArg (fun t => t.app K) key

/-- **The comparisons of derived étale pullbacks on the models and on the small étale sites are
compatible with composition**: for étale `f : X ⟶ Y` and `g : Y ⟶ Z`, the comparison
`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackOfEtaleTransportIso` along `f ≫ g`, read
through `Lf^* Lg^* ≅ L(f ≫ g)^*` on the models and `D(g^*) ⋙ D(f^*) ≅ D((f ≫ g)^*)` on the small
étale sites, is the composite of the comparisons along `g` and `f`. -/
theorem spacesEtaleModelDerivedPullbackOfEtaleTransportIso_comp
    (K : DerivedCategory (spacesEtaleModelRingedTopos B S hS Z).Modules) :
    haveI := etaleModulePullback_additive B S hS f hf
    haveI := preservesFiniteLimits_etaleModulePullback B S hS f hf
    haveI := preservesFiniteColimits_etaleModulePullback B S hS f hf
    haveI := etaleModulePullback_additive B S hS g hg
    haveI := preservesFiniteLimits_etaleModulePullback B S hS g hg
    haveI := preservesFiniteColimits_etaleModulePullback B S hS g hg
    haveI := etaleModulePullback_additive B S hS (f ≫ g) hfg
    haveI := preservesFiniteLimits_etaleModulePullback B S hS (f ≫ g) hfg
    haveI := preservesFiniteColimits_etaleModulePullback B S hS (f ≫ g) hfg
    (spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory.map
        ((spacesEtaleModelDerivedPullbackCompIso B S hS f g).hom.app K) ≫
      (spacesEtaleModelDerivedPullbackOfEtaleTransportIso B S hS (f ≫ g) hfg).hom.app K =
    (spacesEtaleModelDerivedPullbackOfEtaleTransportIso B S hS f hf).hom.app
        ((derivedPullback (spacesEtaleModelHom B S hS g)).obj K) ≫
      (etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory.map
        ((spacesEtaleModelDerivedPullbackOfEtaleTransportIso B S hS g hg).hom.app K) ≫
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
        (etaleModulePullback.{u, u} B S hS g hg) (etaleModulePullback.{u, u} B S hS f hf)).inv.app
          ((spacesEtaleModelModulesEquiv B S hS Z).functor.mapDerivedCategory.obj K) ≫
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
        (etaleModulePullbackComp B S hS f g hf hg hfg)).hom.app
          ((spacesEtaleModelModulesEquiv B S hS Z).functor.mapDerivedCategory.obj K) := by
  have := etaleModulePullback_additive B S hS f hf
  have := preservesFiniteLimits_etaleModulePullback B S hS f hf
  have := preservesFiniteColimits_etaleModulePullback B S hS f hf
  have := etaleModulePullback_additive B S hS g hg
  have := preservesFiniteLimits_etaleModulePullback B S hS g hg
  have := preservesFiniteColimits_etaleModulePullback B S hS g hg
  have := etaleModulePullback_additive B S hS (f ≫ g) hfg
  have := preservesFiniteLimits_etaleModulePullback B S hS (f ≫ g) hfg
  have := preservesFiniteColimits_etaleModulePullback B S hS (f ≫ g) hfg
  have := preservesFiniteLimits_spacesEtaleModelHom_pullbackTopos B S hS f hf
  have := preservesFiniteLimits_spacesEtaleModelHom_pullbackTopos B S hS g hg
  have := preservesFiniteLimits_spacesEtaleModelHom_pullbackTopos B S hS (f ≫ g) hfg
  obtain ⟨_, _, _⟩ := exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS X)
  obtain ⟨_, _, _⟩ := exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS Y)
  obtain ⟨_, _, _⟩ := exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS Z)
  have h := spacesEtaleModelDerivedPullbackCompIso_hom_app_comp_isoOfEtale B S hS f g hf hg hfg
  rw [← Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_comp_isoOfNatIso_hom] at h
  exact comp_coherence_isoWhiskerRight_trans
    (spacesEtaleModelDerivedPullbackIsoOfEtale B S hS f hf)
    (spacesEtaleModelDerivedPullbackIsoOfEtale B S hS g hg)
    (spacesEtaleModelDerivedPullbackIsoOfEtale B S hS (f ≫ g) hfg)
    (spacesEtaleModelDerivedPullbackCompIso B S hS f g).hom _ _ h _ _ _
    (Stacks.DerivedCategoryComparisons.mapDerivedCategorySquare_comp_coherence
      (spacesEtaleModelPullbackComp B S hS f g) (etaleModulePullbackComp B S hS f g hf hg hfg)
      (Functor.isoWhiskerRight (spacesEtaleModelPullbackIsoPushforward B S hS f hf)
          (spacesEtaleModelModulesEquiv B S hS X).functor ≪≫
        spacesEtaleModelModulesEquivPostcompIso B S hS f hf)
      (Functor.isoWhiskerRight (spacesEtaleModelPullbackIsoPushforward B S hS g hg)
          (spacesEtaleModelModulesEquiv B S hS Y).functor ≪≫
        spacesEtaleModelModulesEquivPostcompIso B S hS g hg)
      (Functor.isoWhiskerRight (spacesEtaleModelPullbackIsoPushforward B S hS (f ≫ g) hfg)
          (spacesEtaleModelModulesEquiv B S hS X).functor ≪≫
        spacesEtaleModelModulesEquivPostcompIso B S hS (f ≫ g) hfg)
      (spacesEtaleModelPullbackIsoPushforward_trans_modulesEquivPostcompIso_comp
        B S hS f g hf hg hfg)) K

end Comp

end AlgebraicGeometry.Space

end
