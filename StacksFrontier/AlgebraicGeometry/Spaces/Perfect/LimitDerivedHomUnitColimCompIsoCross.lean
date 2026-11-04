module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnitColimCrossPullback
public import StacksFrontier.CategoryTheory.Functor.Derived.LimitDerivedHomUnitColimCompIsoConjugateFac

/-!
# The defining factorisation of the crossing isomorphism of the pullback datum

`AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataModelIso` crosses between the derived
pullback along the morphism of models of the ringed spaces-étale sites and the inverse image of
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`.  It is built by
`CategoryTheory.Functor.totalLeftDerivedConjugateIso`, that is by uniqueness of right Kan
extensions, so it is pinned down by the one factorisation through the comparisons of derived and
underived pullback that uniqueness provides.  That factorisation is what this file records, and it
is what any statement comparing the crossing isomorphism with anything else has to go through.

The factorisation is stated for the *transported* comparison
`AlgebraicGeometry.Space.spacesEtaleModelTransportedPullbackComparison`: the comparison
`Lf^* ∘ Q ⟶ Q ∘ f^*` of Stacks 06YY on the small étale sites, read on the homotopy categories of
the models through the identification of the localization functors and the comparison of the two
homotopy-level pullbacks.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleModelTransportedPullbackComparison`: the comparison of
  Stacks 06YY on the small étale sites, transported to the models.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataModelIso_hom_app_comp`: **the defining
  factorisation of the crossing isomorphism** — at a complex, the crossing isomorphism followed by
  the transported comparison is the image of the comparison on the models.

## References

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

/-- **The comparison of derived and underived pullback on the small étale sites, transported to
the models.**  The identification `AlgebraicGeometry.Space.spacesEtaleModelModulesFactorsh` of the
localization functors, the comparison
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackComparison` of Stacks 06YY, and the
comparison `AlgebraicGeometry.Space.smallEtaleModulePullbackOnHomotopyModelIso` of the two
homotopy-level pullbacks, composed. -/
def spacesEtaleModelTransportedPullbackComparison {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    DerivedCategory.Qh ⋙ spacesEtaleModelModulesDerivedFunctor B S hS Y ⋙
        (smallEtaleDerivedPullbackData B S hS).pull f ⟶
      (spacesEtaleModelHom B S hS f).pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⋙ spacesEtaleModelModulesDerivedFunctor B S hS X :=
  haveI := hasDerivedModulePullbacks B S hS f
  Functor.whiskerRight (spacesEtaleModelModulesFactorsh B S hS Y).inv
      ((smallEtaleDerivedPullbackData B S hS).pull f) ≫
    Functor.whiskerLeft (spacesEtaleModelModulesHomotopyFunctor B S hS Y)
      (smallEtaleDerivedModulePullbackComparison B S hS f) ≫
    (smallEtaleModulePullbackOnHomotopyModelIso B S hS f
      (spacesEtaleModelModulesPullbackIso B S hS f)).inv

/-- **The defining factorisation of the crossing isomorphism of the pullback datum.**  At a
complex `M`, the crossing isomorphism
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataModelIso`, followed by the transported
comparison, is the image under the derived equivalence of Stacks 03G1 of the comparison of
derived and underived pullback on the models.

This is `CategoryTheory.Functor.totalLeftDerivedConjugateIso_hom_app_comp`: the crossing
isomorphism is built by uniqueness of right Kan extensions, and this is the factorisation that
uniqueness provides. -/
theorem smallEtaleDerivedPullbackDataModelIso_hom_app_comp {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (M : HomotopyCategory (spacesEtaleModelRingedTopos B S hS Y).Modules
      (ComplexShape.up ℤ)) :
    (smallEtaleDerivedPullbackDataModelIso B S hS f).hom.app (DerivedCategory.Qh.obj M) ≫
        (spacesEtaleModelTransportedPullbackComparison B S hS f).app M =
      (spacesEtaleModelModulesDerivedFunctor B S hS X).map
        ((derivedPullbackComparison (spacesEtaleModelHom B S hS f)).app M) := by
  have := hasDerivedModulePullbacks B S hS f
  have h := Functor.totalLeftDerivedConjugateIso_hom_app_comp
    (spacesEtaleModelModulesDerivedFunctor B S hS X) _ _
    (HomotopyCategory.quasiIso (spacesEtaleModelRingedTopos B S hS Y).Modules
      (ComplexShape.up ℤ))
    (smallEtaleModuleQuasiIso B S hS Y)
    (pullbackOnHomotopy (X := spacesEtaleModelRingedTopos B S hS X)
      (Y := spacesEtaleModelRingedTopos B S hS Y) (spacesEtaleModelHom B S hS f))
    (smallEtaleModulePullbackOnHomotopy B S hS f) (spacesEtaleModelModulesFactorsh B S hS Y)
    (smallEtaleModulePullbackOnHomotopyModelIso B S hS f
      (spacesEtaleModelModulesPullbackIso B S hS f)) M
  simp only [spacesEtaleModelTransportedPullbackComparison, smallEtaleDerivedPullbackDataModelIso,
    smallEtaleDerivedModulePullbackModelIso, NatTrans.comp_app]
  exact h

end AlgebraicGeometry.Space

end
