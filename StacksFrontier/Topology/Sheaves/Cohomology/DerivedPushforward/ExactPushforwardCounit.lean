module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional

/-!
# The derived counit of `Lf^* ⊣ Rf_*` when pushforward is exact

Let `f : X ⟶ Y` be a morphism of ringed spaces whose pushforward of sheaves of modules is
exact — the case of a closed immersion, Tag 08KS.  The derived adjunction
`Lf^* ⊣ Rf_*` of Tag 079W is built by Maltsiniotis' theorem out of the homotopy-category
adjunction, so its counit is a right-derived descent and is described only through the
factorization `derivedAdjunction_counit_fac`, which computes not the counit but the counit
precomposed with the derived pullback of the comparison `Qh ∘ f_* ⟶ Rf_* ∘ Qh`.

This file removes that precomposition.  When `f_*` is exact the comparison is invertible at
*every* object of the homotopy category, not merely at the K-injective ones, so the
factorization can be solved and the derived counit is computed at every object of the form
`Qh.obj K`.

## Main definitions

There are no new definitions.

## Main results

* `Stacks.Cohomology.ExactPushforwardAdjunction.isIso_derivedPushforwardUnit_app`: for an exact
  pushforward the comparison `Qh (f_* K) ⟶ Rf_* (Qh K)` is invertible at every object of the
  homotopy category.
* `Stacks.Cohomology.ExactPushforwardAdjunction.derivedAdjunction_counit_app_eq`: **the derived
  counit, computed.**  At `Qh.obj K` it is the inverse of the derived pullback of that
  comparison, followed by the derived pullback comparison and the counit of the
  homotopy-category adjunction.

## Implementation notes

*Why exactness makes the comparison invertible everywhere.*  Invertibility of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit` is known
only on K-injective complexes, by
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces`'s
`isIso_derivedPushforwardUnit_app_of_isKInjective`,
which is what a right derived functor computed by K-injective resolutions gives.  For an exact
functor there is a second model of the total right derived functor, the functor
`Functor.mapDerivedCategory` it induces on derived categories directly, and
`Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived_fac_app` exhibits the comparison
of the chosen model as a composite of two components of isomorphisms of functors.  No resolution
of `K` is involved, so no hypothesis on `K` survives.

*Why this is stated at `Qh.obj K` and not at a general object.*  Every object of the derived
category is isomorphic to `Qh.obj K` for some `K`, `DerivedCategory.Qh` being a localization
functor, and the counit is natural; but the isomorphism is not canonical, so a statement at a
general object would have to quantify over a chosen representative.  The form below is the one
`derivedAdjunction_counit_fac` has and the one consumers that start from a cochain complex
need.

*What this does not do.*  It computes the derived counit in terms of the *underived* counit of
`f^* ⊣ f_*` and the derived pullback comparison.  Carrying that computation through a stalk
functor needs the compatibility of the stalk formula for an underived pullback
(`Stacks.ModuleSkyscraper.pullbackStalkIso`) with the underived counit.  That compatibility is
`Stacks.ModuleSkyscraper.extendScalars_map_pushStalkMap_comp_counit`, the mate of the stalk
formula of Tag 0098 under `f^* ⊣ f_*`: its right-hand side is `pullbackStalkIso` followed by the
stalk of the counit, which is exactly the composite this computation meets.  It is not reached by
unfolding `pullbackStalkIso`, which is constructed by conjugating
`Stacks.ModuleSkyscraper.pushSkyIso` across the two *skyscraper* adjunctions, so nothing in that
construction mentions `RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction`; the mate
lemma supplies it instead.  What carrying the computation to the derived category still needs is
the derived counit of an exact pushforward, computed here, together with the derived form of the
stalk of a pushforward, `AlgebraicGeometry.derivedPushStalkFunctorIso`.

## References

* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

noncomputable section

namespace Stacks.Cohomology.ExactPushforwardAdjunction

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [PreservesFiniteColimits (modulePushforward f)]

/-- **For an exact pushforward the derived-pushforward comparison is invertible everywhere.**
The canonical map `Qh (f_* K) ⟶ Rf_* (Qh K)` out of the homotopy category is an isomorphism at
every object `K`, with no K-injectivity hypothesis.

The functor `(f_*).mapDerivedCategory` induced on derived categories is a second model of the
same total right derived functor, and
`Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived_fac_app` writes the comparison of
the chosen model as the composite of a component of `Functor.mapDerivedCategoryFactorsh` with a
component of the comparison of the two models.  Both are components of isomorphisms of
functors.

It is an instance so that `CategoryTheory.inv` of the derived pullback of the comparison
elaborates in the statement of `derivedAdjunction_counit_app_eq`. -/
instance isIso_derivedPushforwardUnit_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit f).app K) := by
  have h1 : IsIso ((modulePushforward f).mapDerivedCategoryFactorsh.inv.app K) := inferInstance
  have h2 : IsIso ((Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived
      (modulePushforward f)).hom.app (DerivedCategory.Qh.obj K)) := inferInstance
  rw [← Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived_fac_app
    (modulePushforward f) K]
  exact IsIso.comp_isIso' h1 h2

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- **The derived counit of `Lf^* ⊣ Rf_*`, computed, for an exact pushforward.**  At an object
of the form `Qh.obj K` the counit `Lf^* (Rf_* (Qh K)) ⟶ Qh K` is

`(Lf^* of the comparison)⁻¹ ≫ (derived pullback comparison at f_* K) ≫ Qh (underived counit)`.

This is `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_counit_fac` solved
for the counit, which `isIso_derivedPushforwardUnit_app` makes possible.  It is the only
description of the derived counit below `DerivedCategory.Qh` in the library. -/
theorem derivedAdjunction_counit_app_eq
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedAdjunction f).counit.app (DerivedCategory.Qh.obj K) =
      inv ((derivedPullback f).map ((derivedPushforwardUnit f).app K)) ≫
        (derivedPullbackComparison f).app
            (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map
            ((homotopyPullbackPushforwardAdjunction f).counit.app K) := by
  rw [IsIso.eq_inv_comp]
  exact derivedAdjunction_counit_fac f K

end Stacks.Cohomology.ExactPushforwardAdjunction

end

end
