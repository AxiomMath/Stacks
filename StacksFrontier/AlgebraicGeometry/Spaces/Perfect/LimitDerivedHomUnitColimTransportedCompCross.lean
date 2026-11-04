module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnitColimCompIsoCross
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PullbackDataReconcile
public import StacksFrontier.CategoryTheory.Localization.LimitDerivedHomUnitColimTransportedCompModel
/-!
# The transported comparison of 09RI's pullback datum, componentwise

`AlgebraicGeometry.Space.spacesEtaleModelTransportedPullbackComparison` is the comparison of
derived and underived inverse image on the small étale sites, read on the homotopy categories of
the spaces-étale models.  This file computes its components: at a complex `M`, the transported
comparison is the inverse image of the identification
`AlgebraicGeometry.Space.spacesEtaleModelModulesFactorsh` of the localization functors, then the
comparison of `AlgebraicGeometry.Space.derivedModulePullbackLeftDerived`, then the image of the
identification `AlgebraicGeometry.Space.spacesEtaleModelPullbackHomotopyIso` of the two degreewise
inverse images, then the identification of the localization functors again.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleModelPullbackHomotopyIso`: the identification
  `AlgebraicGeometry.Space.spacesEtaleModelModulesPullbackIso` of the two inverse images of
  `𝒪`-modules, applied degreewise.

## Main results

* `AlgebraicGeometry.Space.spacesEtaleModelTransportedPullbackComparison_app`: **the transported
  comparison, componentwise.**

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The identification of the two inverse images of `𝒪`-modules on homotopy categories.**
`AlgebraicGeometry.Space.spacesEtaleModelModulesPullbackIso` applied degreewise, read between the
degreewise pullback along the morphism of models of the ringed spaces-étale sites and the one
along the morphism of small étale ringed topoi of Stacks 03G8. -/
def spacesEtaleModelPullbackHomotopyIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (spacesEtaleModelHom B S hS f).pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        spacesEtaleModelModulesHomotopyFunctor B S hS X ≅
      spacesEtaleModelModulesHomotopyFunctor B S hS Y ⋙
        smallEtaleModulePullbackMapHomotopy (B := B) (S := S) (hS := hS) f :=
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS X)).1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv B S hS Y)).1
  haveI : ((spacesEtaleModelHom B S hS f).pullbackTopos ⋙
      (spacesEtaleModelModulesEquiv B S hS X).functor).Additive :=
    Functor.additive_of_preserves_binary_products _
  Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ) ≪≫
    Stacks.Homology.mapHomotopyCategoryIso (spacesEtaleModelModulesPullbackIso B S hS f)
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ)).symm

/-- **The transported comparison of derived and underived inverse image, componentwise.**
At a complex `N` of `𝒪`-modules on the model of `Y`, the comparison
`AlgebraicGeometry.Space.spacesEtaleModelTransportedPullbackComparison` is the inverse image of
the identification `AlgebraicGeometry.Space.spacesEtaleModelModulesFactorsh` of the localization
functors, then the comparison of `AlgebraicGeometry.Space.derivedModulePullbackLeftDerived`, then
the image under localization of
`AlgebraicGeometry.Space.spacesEtaleModelPullbackHomotopyIso`, then the identification of the
localization functors on the model of `X`. -/
theorem spacesEtaleModelTransportedPullbackComparison_app {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (N : HomotopyCategory (spacesEtaleModelRingedTopos B S hS Y).Modules
      (ComplexShape.up ℤ)) :
    (spacesEtaleModelTransportedPullbackComparison B S hS f).app N =
      ((smallEtaleDerivedPullbackData B S hS).pull f).map
          ((spacesEtaleModelModulesFactorsh B S hS Y).inv.app N) ≫
        ((derivedModulePullbackLeftDerived B S hS).α f).app
            ((spacesEtaleModelModulesHomotopyFunctor B S hS Y).obj N) ≫
          DerivedCategory.Qh.map ((spacesEtaleModelPullbackHomotopyIso B S hS f).inv.app N) ≫
            (spacesEtaleModelModulesFactorsh B S hS X).hom.app
              (((spacesEtaleModelHom B S hS f).pullbackTopos.mapHomotopyCategory
                (ComplexShape.up ℤ)).obj N) :=
  have := hasDerivedModulePullbacks B S hS f
  Stacks.CategoryTheory.ModelComparison.transported_app
    (kX := (spacesEtaleModelModulesFactorsh B S hS X).symm)
    (kY := (spacesEtaleModelModulesFactorsh B S hS Y).symm)
    (χf := spacesEtaleModelPullbackHomotopyIso B S hS f)
    (af := (derivedModulePullbackLeftDerived B S hS).α f)
    (Θf := smallEtaleModulePullbackOnHomotopyModelIso B S hS f
      (spacesEtaleModelModulesPullbackIso B S hS f))
    (tf := spacesEtaleModelTransportedPullbackComparison B S hS f) rfl rfl N

end AlgebraicGeometry.Space

end
