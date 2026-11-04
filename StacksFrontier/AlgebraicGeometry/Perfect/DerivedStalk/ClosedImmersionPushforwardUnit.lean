module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.ClosedImmersionPushforward

/-!
# The derived-pushforward comparison, read through `Ri_* ≅ i_*`

Let `i : Z ⟶ X` be a morphism of ringed spaces along which pushforward of sheaves of modules is
exact, for instance a closed immersion (Stacks 08KS). Then `Ri_*` is isomorphic to the functor
`i_*` induces on derived categories, by
`Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory`. This file shows that this
isomorphism carries the comparison
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit` of the chosen total
right derived functor to the factorization `Functor.mapDerivedCategoryFactorsh` of the induced
functor.

## Main results

* `Stacks.ClosedImmersion.derivedPushforwardUnit_app_comp_derivedPushforwardIsoMapDerivedCategory`:
  the comparison `i_* K ⟶ Ri_* K` out of the homotopy category, followed by the isomorphism
  `Ri_* ≅ i_*`, is the factorization of `i_*` on derived categories.
* `derivedPushforwardUnit_app_comp_derivedPushforwardIsoMapDerivedCategoryOfSchemes`, in the same
  namespace: the same for a closed immersion of schemes.

## Implementation notes

The proof closes `φ ≫ 𝟙 _ = φ` with `simp`: `rw [Category.comp_id]` does not find the pattern,
because the identity's object is spelled through `Functor.mapDerivedCategory` of the pushforward
and the `Category` instance `rw` matches at reducible transparency is not the one the goal
carries.

## References

* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

noncomputable section

namespace Stacks.ClosedImmersion

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The canonical map `i_* K ⟶ Ri_* K` of the chosen total right derived functor, followed by the
isomorphism `Ri_* ≅ i_*` of `derivedPushforwardIsoMapDerivedCategory`, is the factorization of
`i_*` through the localization of the homotopy category. -/
theorem derivedPushforwardUnit_app_comp_derivedPushforwardIsoMapDerivedCategory
    {Z X : RingedSpace.{u, u}} (i : Z ⟶ X)
    [PreservesFiniteColimits (modulePushforward i)]
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit i).app M ≫
        (derivedPushforwardIsoMapDerivedCategory i).hom.app (DerivedCategory.Qh.obj M) =
      (modulePushforward i).mapDerivedCategoryFactorsh.inv.app M := by
  rw [derivedPushforwardIsoMapDerivedCategory, Iso.symm_hom,
    ← mapDerivedCategoryIsoTotalRightDerived_fac_app (modulePushforward i) M,
    Category.assoc, Iso.hom_inv_id_app]
  simp

/-- `derivedPushforwardUnit_app_comp_derivedPushforwardIsoMapDerivedCategory` for a closed
immersion of schemes. -/
theorem derivedPushforwardUnit_app_comp_derivedPushforwardIsoMapDerivedCategoryOfSchemes
    {Z X : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit
          i.toLRSHom.toShHom).app M ≫
        (derivedPushforwardIsoMapDerivedCategoryOfSchemes i).hom.app
          (DerivedCategory.Qh.obj M) =
      (modulePushforward i.toLRSHom.toShHom).mapDerivedCategoryFactorsh.inv.app M :=
  derivedPushforwardUnit_app_comp_derivedPushforwardIsoMapDerivedCategory _ M

end Stacks.ClosedImmersion

end

end
