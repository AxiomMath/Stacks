module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.SupportedPushforward

/-!
# Closed support is preserved by derived direct image from an open subscheme

Let `X` be a scheme, `U ⊆ X` an open subscheme, `j : U ⟶ X` the inclusion and `T ⊆ X` an
arbitrary **closed** subset. If every cohomology sheaf of an object `E` of `D(𝒪_U)` is supported
on the preimage of `T` in `U`, then every cohomology sheaf of `Rj_* E` is supported on `T`, where
`Rj_*` is the chosen derived direct image `Stacks.Duality.derivedPushforward j`.

This is the scheme-level reading of
`Stacks.DerivedQCoh.cohomologySupportedOn_derivedPushforward_of_isClosed`, which is the
open-immersion case of [Stacks, Tag 08DF] for a ringed space and an arbitrary right derived
functor of `j_*`. It is the form that the dévissage of [Stacks, Tag 09T6] in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/ComparisonEquivalence.lean` consumes.

## Main results

* `Stacks.DerivedQCoh.cohomologySupportedOn_derivedPushforward_scheme` is the statement above.

## Implementation notes

Three identifications are spent here, all of them definitional.

* A scheme is a ringed space through `AlgebraicGeometry.LocallyRingedSpace.toRingedSpace`, and
  `structureSheafRing X.toRingedSpace` is `X.ringCatSheaf`: both compose the
  structure sheaf with the forgetful functor `CommRingCat ⥤ RingCat`. Consequently
  `SheafOfModules (ExtensionByZeroModules.resRing U (structureSheafRing X.toRingedSpace))` is
  `U.toScheme.Modules`, which is the identification already recorded in the implementation notes
  of `StacksFrontier/AlgebraicGeometry/Duality/OpenImmersion/DerivedRestrictUnit.lean`, and the two
  `HasDerivedCategory` instances are the same instance.
* `ExtensionByZeroModules.jPush U X.ringCatSheaf` is Mathlib's
  `AlgebraicGeometry.Scheme.Modules.pushforward U.ι`; this is
  `Stacks.Duality.OpenImmersion.jPush_eq_pushforward`, which is `rfl`. So
  `Stacks.Duality.derivedPushforward U.ι` — the total right derived functor of
  `AlgebraicGeometry.Scheme.Modules.pushforward U.ι` along the localization
  `CategoryTheory.DerivedCategory.Qh` of the homotopy category — is a total right derived functor
  of `j_*` in the sense the ringed-space statement asks for, with
  `CategoryTheory.Functor.totalRightDerivedUnit` for a derivation unit. No transport along
  `Stacks.DerivedQCoh.derivedPushforwardIsoOfCochainUnit` is needed: that comparison is for a
  model presented along the localization of the *cochain* complexes, whereas both this statement
  and `Stacks.Duality.derivedPushforward` are presented along the homotopy category.
* `ExtensionByZeroModules.Usp U` is the open `U` with its subspace topology, so
  `(fun x : Usp U ↦ x.1) ⁻¹' T` is `Subtype.val ⁻¹' T`.

The additivity of `j_*` is `Stacks.DerivedQCoh.jPush_additive`. The derivation unit and its
universal property are passed by name rather than found by instance search: the morphism property
`CategoryTheory.HomotopyCategory.quasiIso` is spelled at `U.toScheme.Modules` by the chosen model
and at `SheafOfModules (resRing U (structureSheafRing X.toRingedSpace))` by the ringed-space
statement, and instance search does not cross the two spellings.

## References

* [Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
* [Stacks Project, Tag 09T6](https://stacks.math.columbia.edu/tag/09T6)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

-- `AlgebraicGeometry` also declares a `CohomologySupportedOn`; this file means the one of
-- `Stacks.Cohomology.PushforwardRestriction`, opened selectively below, so the other is hidden.
open AlgebraicGeometry hiding CohomologySupportedOn
open CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction ExtensionByZeroModules
open Stacks.Cohomology.PushforwardRestriction (CohomologySupportedOn)

universe u

namespace Stacks.DerivedQCoh

/-- **Closed support is preserved by derived direct image from an open subscheme.** Let `U` be an
open subscheme of a scheme `X`, let `T ⊆ X` be closed, and let `E` be an object of `D(𝒪_U)` whose
cohomology sheaves all have vanishing stalks outside the preimage of `T` in `U`. Then every
cohomology sheaf of `Rj_*E` has vanishing stalks outside `T`.

This is the open-immersion case of [Stacks, Tag 08DF] for an arbitrary closed subset of the
ambient space, in the shape the dévissage of [Stacks, Tag 09T6] consumes. It is the ringed-space
statement `Stacks.DerivedQCoh.cohomologySupportedOn_derivedPushforward_of_isClosed` read at the
ringed space underlying `X` and at the chosen model `Stacks.Duality.derivedPushforward U.ι` of
derived direct image, which is a total right derived functor of `j_*` along the localization of
the homotopy category. -/
theorem cohomologySupportedOn_derivedPushforward_scheme (X : Scheme.{u}) :
    ∀ (U : X.Opens) (T : Set X), IsClosed T →
      ∀ E : DerivedCategory (SheafOfModules.{u} U.toScheme.ringCatSheaf),
        CohomologySupportedOn (resRing U X.ringCatSheaf) (Subtype.val ⁻¹' T) E →
          CohomologySupportedOn X.ringCatSheaf T
            ((Stacks.Duality.derivedPushforward U.ι).obj E) := by
  intro U T hT E hE
  have hadd : (jPush U (structureSheafRing X.toRingedSpace)).Additive :=
    jPush_additive (structureSheafRing X.toRingedSpace) U
  have hRj : (Stacks.Duality.derivedPushforward U.ι).IsRightDerivedFunctor
      ((Stacks.Duality.homotopyPushforward U.ι).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso U.toScheme.Modules (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso U.toScheme.Modules (ComplexShape.up ℤ)) := inferInstance
  exact cohomologySupportedOn_derivedPushforward_of_isClosed X.toRingedSpace U T hT
    (hjPush := hadd)
    (Rj := Stacks.Duality.derivedPushforward U.ι)
    (αj := (Stacks.Duality.homotopyPushforward U.ι).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso U.toScheme.Modules (ComplexShape.up ℤ)))
    (hRj := hRj) (E := E) (hE := hE)

end Stacks.DerivedQCoh

end
