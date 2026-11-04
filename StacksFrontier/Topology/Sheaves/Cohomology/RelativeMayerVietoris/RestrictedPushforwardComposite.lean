module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.KInjectiveRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.CanonicalDerivedTriangle

/-!
# The restricted derived direct image of a cover is a composite

The relative Mayer--Vietoris triangle of [Stacks, Tag 08HZ] has at its outer vertices the right
derived functors of the composites
`Stacks.Cohomology.RelativeMayerVietoris.restrictedPushforwardAlong f i = i^* ⋙ (i ≫ f)_*`, taken
one functor at a time: nowhere does a functor `D(𝒪_X) ⥤ D(𝒪_U)` occur, so the triangle says
nothing, on its face, about `R(f|_U)_*` applied to `E|_U`. This file supplies the missing
identification: for an open immersion `i : U ⟶ X` the canonical right derived functor of
`restrictedPushforwardAlong f i` *is* derived restriction along `i` followed by the derived direct
image along `i ≫ f`.

## Main results

* `Stacks.Cohomology.RelativeMayerVietoris.canonicalRestrictedPushforwardIso`: the canonical right
  derived functor of `i^* ⋙ (i ≫ f)_*` is `Ri^* ⋙ R(i ≫ f)_*`, for any choices of right derived
  functors on the two factors.

## Implementation notes

Both sides are right derived functors of the same functor on homotopy categories, so the
identification is the uniqueness of right derived functors,
`CategoryTheory.Functor.rightDerivedNatIso`. That the composite of the two chosen derived functors
*is* a right derived functor of the composite is
`Stacks.Cohomology.composite_isRightDerivedFunctor`, whose hypothesis — that the second unit is
invertible on the image of a K-injective complex — holds because inverse image along an open
immersion carries K-injective complexes to K-injective complexes ([Stacks, Tag 08BS],
`Stacks.Cohomology.openImmersionModulePullback_preservesKInjective`). This is the same argument
that `Stacks.Cohomology.derivedPushforwardRestrictIso` makes for [Stacks, Tag 08FE]; only the
functor whose derived functor is being factored is different.

The two sides are compared through
`CategoryTheory.Functor.mapHomotopyCategoryCompIso`, which identifies the degreewise image of a
composite with the composite of the degreewise images; no content beyond associativity enters.

No `@[stacks]` attribute is placed: no tag states this factorisation. It is the bookkeeping that
makes [Stacks, Tag 08HZ] usable, the source taking the identification for granted by writing
`Rf_*(E|_U)` for the restricted direct image.

## References

* [Stacks Project, Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 08BS](https://stacks.math.columbia.edu/tag/08BS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.RelativeMayerVietoris

attribute [local instance] HasDerivedCategory.standard

/-- **The canonical derived functor of "restrict to `U`, then push forward" is a composite.** Let
`f : X ⟶ Y` be a morphism of ringed spaces and let `i : U ⟶ X` be an open immersion. Let `Ri` be a
right derived functor of inverse image along `i` and `Rg` one of direct image along `i ≫ f`. Then
the canonical right derived functor of
`Stacks.Cohomology.RelativeMayerVietoris.restrictedPushforwardAlong f i` is `Ri ⋙ Rg`.

This is what turns the vertices of the relative Mayer--Vietoris triangle of [Stacks, Tag 08HZ]
into derived direct images of restrictions. Restriction along an open immersion is exact, so `Ri`
may always be taken to be the functor induced on derived categories, with no derivation. -/
def canonicalRestrictedPushforwardIso {X Y U : RingedSpace.{u, u}} (f : X ⟶ Y) (i : U ⟶ X)
    [SheafedSpace.IsOpenImmersion i]
    (Ri : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing U)))
    (Rg : DerivedCategory (SheafOfModules.{u} (structureSheafRing U)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (αi : (modulePullback i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Ri)
    (αg : (modulePushforward (i ≫ f)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rg)
    [Ri.IsRightDerivedFunctor αi (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [Rg.IsRightDerivedFunctor αg (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))] :
    canonicalRightDerived (restrictedPushforwardAlong f i) ≅ Ri ⋙ Rg := by
  let I := (modulePullback i).mapHomotopyCategory (ComplexShape.up ℤ)
  let G := (modulePushforward (i ≫ f)).mapHomotopyCategory (ComplexShape.up ℤ)
  let βg : (I ⋙ G) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ (Ri ⋙ Rg) :=
    Functor.whiskerLeft I αg ≫ Functor.whiskerRight αi Rg
  let W := HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
    (ComplexShape.up ℤ)
  have : (Ri ⋙ Rg).IsRightDerivedFunctor βg W :=
    composite_isRightDerivedFunctor
      (DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective X)
      (modulePullback i) (modulePushforward (i ≫ f)) Ri Rg αi αg fun K _ ↦
        (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
          (G ⋙ DerivedCategory.Qh)
          (DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective U)).2
          DerivedCategory.Qh Rg αg
          (((modulePullback i).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          (openImmersionModulePullback_preservesKInjective i K)
  exact Functor.rightDerivedNatIso _ (Ri ⋙ Rg)
    (canonicalRightDerivedUnit (restrictedPushforwardAlong f i)) βg W
    (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (modulePullback i ⋙ modulePushforward (i ≫ f)))
      (ComplexShape.up ℤ)).symm DerivedCategory.Qh)

end Stacks.Cohomology.RelativeMayerVietoris

end
