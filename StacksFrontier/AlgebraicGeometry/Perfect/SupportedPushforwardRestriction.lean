module

public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.ExtensionByZero
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportDetectedOnOneOpen

/-!
# Restricting the derived pushforward of a supported object back to the open

Let `(X, 𝒪)` be a space with a sheaf of rings, `U ⊆ X` an open, and `T ⊆ U` a closed subset of
`X`. For an object `F` of `D(𝒪_U)` whose cohomology is supported on the preimage of `T`,
restriction along `U ⟶ X` undoes the derived pushforward: `(Rj_*F)|_U ≅ F`.

Both of the facts below are two or three lines from results in the library. By part (2) of
[Stacks, Tag 08DF] the canonical map from extension by zero to derived pushforward is invertible
at such an `F`, so `Rj_*F ≅ j_!F`; extension by zero keeps the support; and restriction undoes
extension by zero outright, the unit of `j_! ⊣ j^*` being invertible —
`Stacks.LimitHomDescent.restrictionExtensionIso`.

## Main results

* `Stacks.Perfect.SupportedPushforward.cohomologySupportedOn_derivedPushforward_of_supported`:
  the pushforward keeps the support.
* `Stacks.Perfect.SupportedPushforward.derivedRestriction_derivedPushforward_isoOfSupported`:
  the isomorphism `(Rj_*F)|_U ≅ F`.

## Where this is used

It is the clause of [Stacks, Tag 08EK] that recovers `F ⊕ F[1]` at the end. In that proof `F`
lives on a quasi-compact open `U` of an affine `X` and is supported on `T ∩ U`; it is pushed
forward over `W = U ∪ (X ∖ T)`, where `T ∩ W` is both closed in `W` and inside `U`, and the
pushforward is then lifted to `X` by [Stacks, Tag 08EI]. Restricting the lift back past `W` to
`U` has to give `F` again, and this is what says so.

## Implementation notes

Stated at the **standard** derived-category model. That is forced rather than chosen:
`Stacks.ExtensionByZero.derivedRestriction`, and hence
`Stacks.LimitHomDescent.restrictionExtensionIso`, pins that model, so a statement with the model
as a variable does not typecheck against them — the two `DerivedCategory` instances differ. It is
also the model [Stacks, Tag 08EI] and `Stacks.DerivedQCoh.SupportedDerivedModules` are stated at,
so it is the model the assembly of [Stacks, Tag 08EK] runs in.

## References

* [Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules
open Stacks.Cohomology.PushforwardRestriction

universe u

namespace Stacks.Perfect.SupportedPushforward

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- **The derived pushforward along an open immersion keeps a closed support inside the open.**
If `T` is closed in `X` with `T ⊆ U` and `F` is supported on the preimage of `T`, then `Rj_*F` is
supported on `T`.

By part (2) of [Stacks, Tag 08DF] the canonical map from extension by zero to derived pushforward
is invertible at such an `F`, and extension by zero keeps the support by
`Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_jShriek`; the support then
transports along the isomorphism.

This is the support half of what [Stacks, Tag 08EK] needs from the pushforward, its perfectness
half being [Stacks, Tag 08DP]. The two share their hypotheses: 08DP wants the image of the
support in the ambient space closed, and 08DF(2) wants the support inside the open — which is why
08EK pushes forward over `W = U ∪ (X ∖ T)`, where both hold, rather than over `X`, where neither
does.

**Not the private lemma of the same name.**
`Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_derivedPushforward_of_supported`
exists, `private`, in
`StacksFrontier/Topology/Sheaves/Cohomology/SupportedComplexes/PushforwardAndRestriction.lean`. That
one is stated only for objects of the form `Q.obj I` with `I` a cochain complex, and it is a step
*towards* [Stacks, Tag 08DF] part (2), which uses it. This one is for an arbitrary object and is
proved *from* 08DF(2), so it cannot replace the private one — the dependency runs the other way —
and the private one cannot serve here, being both weaker and inaccessible. Keeping them in
different namespaces is what stops the shared name from being ambiguous: inside that file the name
resolves to the private step, and everywhere else to this. -/
theorem cohomologySupportedOn_derivedPushforward_of_supported
    (U : Opens X) (T : Set X) (hT : IsClosed T) (hTU : T ⊆ (U : Set X))
    [HasDerivedCategory (SheafOfModules.{u} O)]
    [HasDerivedCategory (SheafOfModules.{u} (resRing U O))]
    (Rj : DerivedCategory (SheafOfModules.{u} (resRing U O)) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (αj : (jPush U O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (F : DerivedCategory (SheafOfModules.{u} (resRing U O)))
    (hF : CohomologySupportedOn (resRing U O) ((fun x : Usp U ↦ x.1) ⁻¹' T) F) :
    CohomologySupportedOn O T (Rj.obj F) :=
  have := isIso_extensionByZeroToDerivedPushforward_app_of_supported O U T hT hTU Rj αj F hF
  cohomologySupportedOn_of_iso O T
    (asIso ((extensionByZeroToDerivedPushforward O U Rj αj).app F))
    (cohomologySupportedOn_jShriek O U T F hF)

/-- **Restricting the derived pushforward back to the open recovers the object**, for an object
supported on a closed subset of the open.

`Rj_*F ≅ j_!F` by part (2) of [Stacks, Tag 08DF], and restriction undoes extension by zero by
`Stacks.LimitHomDescent.restrictionExtensionIso`. -/
def derivedRestriction_derivedPushforward_isoOfSupported
    (U : Opens X) (T : Set X) (hT : IsClosed T) (hTU : T ⊆ (U : Set X))
    (Rj : DerivedCategory (SheafOfModules.{u} (resRing U O)) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (αj : (jPush U O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (F : DerivedCategory (SheafOfModules.{u} (resRing U O)))
    (hF : CohomologySupportedOn (resRing U O) ((fun x : Usp U ↦ x.1) ⁻¹' T) F) :
    (Stacks.ExtensionByZero.derivedRestriction O U).obj (Rj.obj F) ≅ F :=
  haveI := isIso_extensionByZeroToDerivedPushforward_app_of_supported O U T hT hTU Rj αj F hF
  (Stacks.ExtensionByZero.derivedRestriction O U).mapIso
      (asIso ((extensionByZeroToDerivedPushforward O U Rj αj).app F)).symm ≪≫
    (Stacks.LimitHomDescent.restrictionExtensionIso O U).app F

end Stacks.Perfect.SupportedPushforward

end
