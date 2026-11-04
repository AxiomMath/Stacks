module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison of Tag 0D5S at arbitrary models

The factorisation `derivedPullbackCompIsoCanonical_hom_app_comp_comparison`, in the namespace
`Stacks.Cohomology.DerivedPushforwardComposition`, at arbitrary models of the three derived
categories.

## Main results

* `derivedPullbackCompIsoCanonical_hom_app_comp_comparison_of_models`: the canonical comparison
  of Tag 0D5S factors the comparison for `L(f ≫ g)^*` through the degreewise
  pullback-composition isomorphism, for arbitrary models of the derived categories.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.Cohomology.DerivedPushforwardComposition

universe u wX wY wZ

noncomputable section Models


/-- The canonical comparison of Tag 0D5S factors the comparison for `L(f ≫ g)^*` through the
degreewise pullback-composition isomorphism.  This is `CategoryTheory.Functor.leftDerived_fac_app`
for the left derived functor `L(f ≫ g)^*`, read through
`Stacks.DerivedPullback.Composition.derivedPullbackCompCounit_app`. -/
theorem derivedPullbackCompIsoCanonical_hom_app_comp_comparison_of_models
    {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasDerivedCategory.{wX} (ModuleSheaves.{u} X)] [HasDerivedCategory.{wY} (ModuleSheaves.{u} Y)]
    [HasDerivedCategory.{wZ} (ModuleSheaves.{u} Z)]
    (W : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) :
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom.app
      (DerivedCategory.Qh.obj W) ≫
        (derivedPullbackComparison (f ≫ g)).app W =
      (derivedPullback f).map ((derivedPullbackComparison g).app W) ≫
        (derivedPullbackComparison f).app
            (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj W) ≫
          DerivedCategory.Qh.map ((Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso f
            g).hom.app W) :=
  (Functor.leftDerived_fac_app (derivedPullback (f ≫ g)) (derivedPullbackComparison (f ≫ g))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))
      (derivedPullback g ⋙ derivedPullback f)
      (Stacks.DerivedPullback.Composition.derivedPullbackCompCounit f g (derivedPullback f)
        (derivedPullback g)
        (derivedPullbackComparison f) (derivedPullbackComparison g)) W).trans
    (Stacks.DerivedPullback.Composition.derivedPullbackCompCounit_app f g (derivedPullback f)
      (derivedPullback g)
      (derivedPullbackComparison f) (derivedPullbackComparison g) W)

end Models

end Stacks.Cohomology.DerivedPushforwardComposition

end
