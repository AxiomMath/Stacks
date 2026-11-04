module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnitColimCompIsoComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelHomCompCocycle

/-!
# The composition law of the crossing isomorphism of 09RI's pullback datum

`AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataModelIso` crosses between the derived
pullback along the morphism of models of the ringed spaces-étale sites and the inverse image of
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`.  This file proves that **the crossing
isomorphisms are compatible with composition**: the one at `f ≫ g` agrees with the one at `g`
followed by the one at `f`, read through the composition comparison of the datum on one side and
`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIso` on the other, given the
factorisation `h₂` of the composition comparison of the datum through the transported comparison
`AlgebraicGeometry.Space.spacesEtaleModelTransportedPullbackComparison`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataModelIso_comp`: **the composition law**,
  from the factorisation `h₂` of the composition comparison of the datum.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
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

/-- **The crossing isomorphisms of 09RI's pullback datum are compatible with composition.**

For composable morphisms `f : X ⟶ Y`, `g : Y ⟶ Z` of algebraic spaces, the crossing isomorphism
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataModelIso` at `f ≫ g`, read through the
composition comparison of `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`, is the crossing
isomorphism at `g` followed by the one at `f`, read through
`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIso`.

The hypothesis `h₂` is the factorisation of the composition comparison of the datum through the
transported comparison `AlgebraicGeometry.Space.spacesEtaleModelTransportedPullbackComparison`:
at a complex of modules on the model of `Z`, the composition comparison followed by the
transported comparison for `f ≫ g` is the transported comparison for `g`, then the one for `f`,
then the image of the composition comparison of the underived inverse images on the models. -/
theorem smallEtaleDerivedPullbackDataModelIso_comp {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z)
    (h₂ : ∀ M : HomotopyCategory (spacesEtaleModelRingedTopos B S hS Z).Modules
        (ComplexShape.up ℤ),
      ((smallEtaleDerivedPullbackData B S hS).compIso f g).inv.app
            ((spacesEtaleModelModulesDerivedFunctor B S hS Z).obj (DerivedCategory.Qh.obj M)) ≫
          (spacesEtaleModelTransportedPullbackComparison B S hS (f ≫ g)).app M =
        ((smallEtaleDerivedPullbackData B S hS).pull f).map
            ((spacesEtaleModelTransportedPullbackComparison B S hS g).app M) ≫
          (spacesEtaleModelTransportedPullbackComparison B S hS f).app
              (((spacesEtaleModelHom B S hS g).pullbackTopos.mapHomotopyCategory
                (ComplexShape.up ℤ)).obj M) ≫
            (spacesEtaleModelModulesDerivedFunctor B S hS X).map (DerivedCategory.Qh.map
              ((Functor.mapHomotopyCategoryCompIso (spacesEtaleModelPullbackComp B S hS f g)
                (ComplexShape.up ℤ)).hom.app M)))
    (K : DerivedCategory (spacesEtaleModelRingedTopos B S hS Z).Modules) :
    ((smallEtaleDerivedPullbackData B S hS).compIso f g).inv.app
          ((spacesEtaleModelModulesDerivedFunctor B S hS Z).obj K) ≫
        (smallEtaleDerivedPullbackDataModelIso B S hS (f ≫ g)).inv.app K =
      ((smallEtaleDerivedPullbackData B S hS).pull f).map
          ((smallEtaleDerivedPullbackDataModelIso B S hS g).inv.app K) ≫
        (smallEtaleDerivedPullbackDataModelIso B S hS f).inv.app
            ((derivedPullback (X := spacesEtaleModelRingedTopos B S hS Y)
              (Y := spacesEtaleModelRingedTopos B S hS Z)
              (spacesEtaleModelHom B S hS g)).obj K) ≫
          (spacesEtaleModelModulesDerivedFunctor B S hS X).map
            ((spacesEtaleModelDerivedPullbackCompIso B S hS f g).hom.app K) := by
  have := hasDerivedModulePullbacks B S hS f
  have := hasDerivedModulePullbacks B S hS g
  have := hasDerivedModulePullbacks B S hS (f ≫ g)
  refine Stacks.CategoryTheory.ModelComparison.comp_comm_postcomp
    (Functor.mapHomotopyCategoryCompIso (spacesEtaleModelPullbackComp B S hS f g)
      (ComplexShape.up ℤ))
    (spacesEtaleModelDerivedPullbackCompIso B S hS f g)
    ((smallEtaleDerivedPullbackData B S hS).compIso f g).symm
    (derivedPullbackComparison (spacesEtaleModelHom B S hS f))
    (derivedPullbackComparison (spacesEtaleModelHom B S hS g))
    (derivedPullbackComparison (spacesEtaleModelHom B S hS (f ≫ g)))
    (spacesEtaleModelTransportedPullbackComparison B S hS f)
    (spacesEtaleModelTransportedPullbackComparison B S hS g)
    (spacesEtaleModelTransportedPullbackComparison B S hS (f ≫ g))
    (smallEtaleDerivedPullbackDataModelIso B S hS f)
    (smallEtaleDerivedPullbackDataModelIso B S hS g)
    (smallEtaleDerivedPullbackDataModelIso B S hS (f ≫ g))
    (spacesEtaleModelDerivedPullbackCompIso_hom_app_comp_derivedPullbackComparison_app B S hS f g)
    ?h₂
    (smallEtaleDerivedPullbackDataModelIso_hom_app_comp B S hS f)
    (smallEtaleDerivedPullbackDataModelIso_hom_app_comp B S hS g)
    (smallEtaleDerivedPullbackDataModelIso_hom_app_comp B S hS (f ≫ g))
    (exists_iso_Qh_isIso_derivedPullbackComparison_spacesEtaleModelHom B S hS (f ≫ g)) K
  intro M
  convert h₂ M using 2
  rfl

end AlgebraicGeometry.Space

end
