module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoheratorFlatPushforwardQcqs
public import StacksFrontier.Homology.Injectives.DerivedCategory.RightDerivedTriangulated

/-!
# The derived direct image of an algebraic space is triangulated

The derived direct image `Φ : D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))` of
`StacksFrontier/AlgebraicGeometry/Spaces/CoheratorFlatPushforwardQcqs.lean` and the derived
coherator `RQ_X : D(𝒪_X) ⥤ D(QCoh(𝒪_X))` of
`StacksFrontier/AlgebraicGeometry/Spaces/Coherator.lean` commute with the shift and send
distinguished triangles to distinguished triangles.

## Main results

* `AlgebraicGeometry.Space.derivedQuasicoherentPushforward_isTriangulated`,
* `AlgebraicGeometry.Space.derivedCoherator_isTriangulated`.

## Implementation notes

Both are total right derived functors along the localization of cochain complexes, so both
are `Stacks.Injectives.isTriangulated_of_complexUnit` at the Grothendieck abelianness of
their source: `AlgebraicGeometry.Space.isGrothendieckAbelian_modules` for the modules and
`AlgebraicGeometry.Space.quasicoherentSheaves_isGrothendieckAbelian` (Stacks 077V (1)) for the
quasi-coherent ones.  The derived direct image of all modules,
`AlgebraicGeometry.Space.derivedModulePushforward`, carries its shift and its triangulated
structure already, from
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentDerivedDirectImage.lean`.

Both functors are defined against the standard model of the derived categories, so that
model has to be available in order to apply a general statement to them; it is introduced in
each proof body, never as an instance of this file.

No Stacks attribute is placed: triangulatedness of `Φ` is not a tagged statement, it is
part of what the source means by a derived functor between derived categories.

## References

* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
* [Stacks Project, Tag 08GZ](https://stacks.math.columbia.edu/tag/08GZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Pushforward

variable {X Y : AlgebraicSpaces B S hS}

/-- **The functor `Φ` of Stacks 08GZ commutes with the shift.** -/
instance derivedQuasicoherentPushforward_commShift (f : X ⟶ Y)
    (hpush : PushforwardPreservesQuasicoherence B S hS f) :
    (derivedQuasicoherentPushforward B S hS f hpush).CommShift ℤ := by
  letI := HasDerivedCategory.standard (QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
  letI := HasDerivedCategory.standard (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2)
  letI : IsGrothendieckAbelian.{u} (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) :=
    quasicoherentSheaves_isGrothendieckAbelian B S hS X.1 X.2
  exact Stacks.Injectives.commShiftOfComplexUnit (quasicoherentPushforward B S hS f hpush)
    (derivedQuasicoherentPushforward B S hS f hpush)
    (derivedQuasicoherentPushforwardUnit B S hS f hpush)

/-- **The functor `Φ` of Stacks 08GZ is triangulated.** -/
instance derivedQuasicoherentPushforward_isTriangulated (f : X ⟶ Y)
    (hpush : PushforwardPreservesQuasicoherence B S hS f) :
    (derivedQuasicoherentPushforward B S hS f hpush).IsTriangulated := by
  let := HasDerivedCategory.standard (QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2)
  let : IsGrothendieckAbelian.{u} (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) :=
    quasicoherentSheaves_isGrothendieckAbelian B S hS X.1 X.2
  exact Stacks.Injectives.isTriangulated_of_complexUnit (quasicoherentPushforward B S hS f hpush)
    (derivedQuasicoherentPushforward B S hS f hpush)
    (derivedQuasicoherentPushforwardUnit B S hS f hpush)

end Pushforward

section Coherator

attribute [local instance] isClosedUnderKernels_quasicoherentSheaves_schemeUniverse
  isClosedUnderCokernels_quasicoherentSheaves quasicoherentSheaves_abelian_of_closure

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The derived coherator commutes with the shift.** -/
instance derivedCoherator_commShift : (derivedCoherator B S hS F hF).CommShift ℤ := by
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS F hF)
  letI := HasDerivedCategory.standard (QuasicoherentSheaves.{u, u} B S hS F hF)
  letI := isGrothendieckAbelian_modules B S hS F hF
  exact Stacks.Injectives.commShiftOfComplexUnit (coherator B S hS F hF)
    (derivedCoherator B S hS F hF) (derivedCoheratorUnit B S hS F hF)

/-- **The derived coherator is triangulated.** -/
instance derivedCoherator_isTriangulated : (derivedCoherator B S hS F hF).IsTriangulated := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS F hF)
  let := HasDerivedCategory.standard (QuasicoherentSheaves.{u, u} B S hS F hF)
  let := isGrothendieckAbelian_modules B S hS F hF
  exact Stacks.Injectives.isTriangulated_of_complexUnit (coherator B S hS F hF)
    (derivedCoherator B S hS F hF) (derivedCoheratorUnit B S hS F hF)

end Coherator

end AlgebraicGeometry.Space

end
