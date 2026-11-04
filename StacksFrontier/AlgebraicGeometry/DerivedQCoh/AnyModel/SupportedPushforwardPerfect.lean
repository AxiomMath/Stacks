module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AnyModel.HomOutOfSupportedPushforward
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AnyModel.RestrictAndPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.LiftingComplexes.SupportInsideTheOpen

/-!
# The derived pushforward of a perfect object supported inside the open is perfect

Let `X` be a scheme, `V ⊆ X` an open subscheme, `j : V ⟶ X` the inclusion and `T ⊆ X` a closed
subset *contained in* `V`. If `K` is a perfect object of `D(𝒪_V)` whose cohomology sheaves are
supported on the preimage of `T`, then `Rj_*K` is a perfect object of `D(𝒪_X)`, where `Rj_*` is
`Stacks.Duality.derivedPushforward j`.

This is [Stacks, Tag 08DP] together with [Stacks, Tag 08DF] part (2), at the locally small model
and for the derived pushforward the compact-generation arguments use. It is the perfectness of
the summand `K = Rj_{V*}K_V` of the generator produced by the inductive step of
[Stacks, Tag 09IS] and [Stacks, Tag 0A9A].

## Main results

* `Stacks.DerivedQCoh.AnyModel.isPerfect_derivedPushforward_of_cohomologySupportedOn` — the
  statement above.

## Implementation notes

**The model is the locally small one.** No `CategoryTheory.HasDerivedCategory` binder appears
below, so instance search supplies the global instances of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`. That is the model at which
[Stacks, Tag 09IS] has content, and the model
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/KoszulDetectionTwoOpens.lean` reads its two hypotheses
at.

**Why a transport is needed, and of what.** [Stacks, Tag 08DP] is
`Stacks.Cohomology.ClosedSupportPerfect.isPerfect_derivedPushforward_of_closedSupport`, and its
scheme-level consequence for extension by zero is
`Stacks.Perfect.LiftingComplexes.isPerfect_jShriek_of_cohomologySupportedOn`; both files seat
`CategoryTheory.HasDerivedCategory.standard` as a file-local instance, so both speak only about
that model. The `j_!` form is therefore *transported* here rather than restated at the locally
small model, which would be a second declaration with the same printed statement. The transport
is `StacksDraft.DerivedModel.mapDerivedCategoryModelIso` for the functor `j_!`,
`Stacks.DerivedQCoh.AnyModel.isPerfect_modelEquiv_iff` for perfectness and
`Stacks.DerivedQCoh.AnyModel.isZero_stalk_homology_modelEquiv_iff` for the support condition,
which is that predicate unfolded. The passage from `j_!` to `Rj_*` needs no transport:
[Stacks, Tag 08DF] part (2) is `Stacks.Cohomology.PushforwardRestriction`'s
`isIso_extensionByZeroToDerivedPushforward_app_of_supported`, which carries its model as a
binder.

**Four instance arguments are supplied as terms, and three local instances are seated by hand.**
`Stacks.ExtensionByZero.jShriek_additive_and_exact` proves the additivity and exactness of `j_!`
by exhibiting adjoints, and they are deliberately not instances; a local `let` does not make them
findable, so they are passed positionally — this is the device of
`Stacks.DerivedQCoh.AnyModel.forall_hom_shift_derivedPushforward_eq_zero_iff`. The additivity of
`j_*` is proved the same way. The three local `let`s in the proof are the recurring spelling
obstruction: `ExtensionByZeroModules.jShriek V X.ringCatSheaf` has source
`SheafOfModules (ExtensionByZeroModules.resRing V X.ringCatSheaf)` and target
`SheafOfModules X.ringCatSheaf`, which are `V.toScheme.Modules` and `X.Modules` definitionally but
not reducibly; `CategoryTheory.HasDerivedCategory` carries the localized category as data, so the
`CategoryTheory.Category` instance of a derived category only resolves when the
`HasDerivedCategory` term it was built from is the one instance search returns. Seating the three
that occur — the standard model on `V` and the locally small model on `X`, each followed by the
`Category` instance it determines — makes them syntactically the same term. Seating the standard
model on `X` as well is what must *not* be done: it shadows the locally small one, which is the
model the conclusion is stated at.

## References

* [Stacks Project, Tag 08DP](https://stacks.math.columbia.edu/tag/08DP)
* [Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules
open Stacks.Cohomology.PerfectComplexes (IsPerfect isClosedUnderIsomorphisms_isPerfect)
open Stacks.Cohomology.PushforwardRestriction (cohomologySupportedOn_of_iso
  isIso_extensionByZeroToDerivedPushforward_app_of_supported)
open StacksDraft.DerivedModel

universe u

namespace Stacks.DerivedQCoh.AnyModel

/-- **The derived pushforward of a perfect object supported inside the open is perfect.** Let `T`
be a closed subset of a scheme `X` contained in an open subscheme `V`, and let `K` be a perfect
object of `D(𝒪_V)` whose cohomology sheaves are supported on the preimage of `T`. Then `Rj_*K` is
a perfect object of `D(𝒪_X)`.

The extension by zero `j_!K` is perfect by [Stacks, Tag 08DP], which is
`Stacks.Perfect.LiftingComplexes.isPerfect_jShriek_of_cohomologySupportedOn` transported from the
standard model to the locally small one; and the comparison `j_!K ⟶ Rj_*K` is invertible on an
object with that support by [Stacks, Tag 08DF] part (2). -/
theorem isPerfect_derivedPushforward_of_cohomologySupportedOn (X : Scheme.{u}) (V : X.Opens)
    (T : Set X) (hT : IsClosed T) (hTV : T ⊆ (V : Set X))
    (K : DerivedCategory V.toScheme.Modules)
    (hK : IsPerfect (X := V.toScheme.toRingedSpace) K)
    (hKT : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn
      V.toScheme.ringCatSheaf (Subtype.val ⁻¹' T) K) :
    IsPerfect (X := X.toRingedSpace) ((Stacks.Duality.derivedPushforward V.ι).obj K) := by
  obtain ⟨h₁, h₂, h₃⟩ := Stacks.ExtensionByZero.jShriek_additive_and_exact X.ringCatSheaf V
  let hjp : (jPush V X.ringCatSheaf).Additive := by
    have : (jPush V X.ringCatSheaf).IsRightAdjoint :=
      (jStarAdjunction V X.ringCatSheaf).isRightAdjoint
    exact Functor.additive_of_preserves_binary_products _
  -- `j_!K` is perfect: the standard-model statement, transported.
  have hshriek : IsPerfect (X := X.toRingedSpace)
      ((jShriek V X.ringCatSheaf).mapDerivedCategory.obj K) := by
    let := h₁
    let := h₂
    let := h₃
    let hXs := HasDerivedCategory.standard X.Modules
    let hXl := AlgebraicGeometry.Scheme.Modules.hasDerivedCategory X
    let hVs := HasDerivedCategory.standard V.toScheme.Modules
    let hVl := AlgebraicGeometry.Scheme.Modules.hasDerivedCategory V.toScheme
    let eV := modelEquiv hVs hVl
    let eX := modelEquiv hXs hXl
    let K' := eV.inverse.obj K
    have hK' : @IsPerfect V.toScheme.toRingedSpace hVs K' :=
      (isPerfect_modelEquiv_iff (X := V.toScheme.toRingedSpace) hVs hVl K').2
        (isClosedUnderIsomorphisms_isPerfect.of_iso (eV.counitIso.app K).symm hK)
    have hKTls : @Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn _
        V.toScheme.ringCatSheaf hVl (Subtype.val ⁻¹' T) (eV.functor.obj K') :=
      cohomologySupportedOn_of_iso _ _ (eV.counitIso.app K).symm hKT
    have hKT' : @Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn _
        V.toScheme.ringCatSheaf hVs (Subtype.val ⁻¹' T) K' := fun i x hx =>
      (isZero_stalk_homology_modelEquiv_iff V.toScheme.ringCatSheaf hVs hVl K' i x).mpr
        (hKTls i x hx)
    have hstd := Stacks.Perfect.LiftingComplexes.isPerfect_jShriek_of_cohomologySupportedOn
      X V T hT hTV K' hK' hKT'
    let : HasDerivedCategory.{u + 1} (SheafOfModules.{u} (resRing V X.ringCatSheaf)) := hVs
    let : Category.{u + 1, u + 1}
      (DerivedCategory (SheafOfModules.{u} (resRing V X.ringCatSheaf))) := inferInstance
    let : HasDerivedCategory.{u} (SheafOfModules.{u} X.ringCatSheaf) := hXl
    let : Category.{u, u + 1} (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) :=
      inferInstance
    refine isClosedUnderIsomorphisms_isPerfect.of_iso
      ((@mapDerivedCategoryModelIso _ _ _ _ _ _ (jShriek V X.ringCatSheaf) h₁ h₂ h₃
        hVs hVl hXs hXl).app K' |>.trans ?_)
      ((isPerfect_modelEquiv_iff (X := X.toRingedSpace) hXs hXl _).1 hstd)
    exact Functor.mapIso _ (eV.counitIso.app K)
  -- `j_!K ⟶ Rj_*K` is invertible on an object supported on `T`.
  have hRD : (Stacks.Duality.derivedPushforward V.ι).IsRightDerivedFunctor
      ((Stacks.Duality.homotopyPushforward V.ι).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso V.toScheme.Modules (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso V.toScheme.Modules (ComplexShape.up ℤ)) := inferInstance
  have hiso :=
    @isIso_extensionByZeroToDerivedPushforward_app_of_supported _ X.ringCatSheaf V T hT hTV
      (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory X)
      (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory V.toScheme)
      (Stacks.Duality.derivedPushforward V.ι)
      ((Stacks.Duality.homotopyPushforward V.ι).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso V.toScheme.Modules (ComplexShape.up ℤ))) hRD K hKT
  exact isClosedUnderIsomorphisms_isPerfect.of_iso (@asIso _ _ _ _ _ hiso) hshriek

end Stacks.DerivedQCoh.AnyModel

end
