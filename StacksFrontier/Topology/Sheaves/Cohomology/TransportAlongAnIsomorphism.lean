module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.AlongAnIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatOpcycles
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback

/-!
# Tor amplitude and perfectness along an isomorphism of ringed spaces

Let `e : X ≅ Y` be an isomorphism of ringed spaces and `E` an object of `D(𝒪_Y)`. Then `E` has
Tor amplitude in `[a, b]` if and only if `Le.hom^* E` does, and `E` is perfect if and only if
`Le.hom^* E` is.

## Main results

* `Stacks.Cohomology.TransportAlongIso.hasTorAmplitude_derivedPullback_iff`
* `Stacks.Cohomology.TransportAlongIso.isPerfect_derivedPullback_iff`

## Implementation notes

Both directions are the one-directional statements for an arbitrary morphism of ringed spaces --
`Stacks.Cohomology.TorAmplitude.Pullback.hasTorAmplitude_derivedPullback` and
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback` -- applied once
along `e.hom` and once along `e.inv`; the round trip is undone by
`Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackHomInvIso`, and both predicates depend
only on the isomorphism class of their argument.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.DerivedPullbackAlongIso (derivedPullbackHomInvIso)

namespace Stacks.Cohomology.TransportAlongIso

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (e : X ≅ Y)

/-- **Tor amplitude transports along an isomorphism of ringed spaces.** An object of `D(𝒪_Y)`
has Tor amplitude in `[a, b]` exactly when its derived pullback along `e` does. -/
theorem hasTorAmplitude_derivedPullback_iff (E : DerivedCategory (OXMod.{u} Y)) (a b : ℤ) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X ((derivedPullback e.hom).obj E) a b ↔
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y E a b := by
  refine ⟨fun h => ?_, Stacks.Cohomology.TorAmplitude.Pullback.hasTorAmplitude_derivedPullback
    e.hom E a b⟩
  exact Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1}
    (Stacks.Cohomology.TorAmplitude.Pullback.hasTorAmplitude_derivedPullback e.inv
      ((derivedPullback e.hom).obj E) a b h)
    ((derivedPullbackHomInvIso e).app E).symm

/-- **Perfectness transports along an isomorphism of ringed spaces.** An object of `D(𝒪_Y)` is
perfect exactly when its derived pullback along `e` is. -/
theorem isPerfect_derivedPullback_iff (E : DerivedCategory (OXMod.{u, u} Y)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) ((derivedPullback e.hom).obj E) ↔
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y) E := by
  refine ⟨fun h => ?_, AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    e.hom E⟩
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
    ((derivedPullbackHomInvIso e).app E)
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback e.inv
      ((derivedPullback e.hom).obj E) h)

/-! ### The scheme-level statements -/

/-- An isomorphism of schemes is an isomorphism of the underlying ringed spaces. -/
def ringedSpaceIsoOfSchemeIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    X.toLocallyRingedSpace.toRingedSpace ≅ Y.toLocallyRingedSpace.toRingedSpace :=
  (Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace).mapIso e

/-- **Tor amplitude transports along an isomorphism of schemes.** -/
theorem hasTorAmplitude_derivedPullback_scheme_iff {X Y : Scheme.{u}} (e : X ≅ Y)
    (E : DerivedCategory (OXMod.{u} Y.toLocallyRingedSpace.toRingedSpace)) (a b : ℤ) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toLocallyRingedSpace.toRingedSpace
        ((derivedPullback (ringedSpaceIsoOfSchemeIso e).hom).obj E) a b ↔
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y.toLocallyRingedSpace.toRingedSpace E a b :=
  hasTorAmplitude_derivedPullback_iff (ringedSpaceIsoOfSchemeIso e) E a b

/-- **Perfectness transports along an isomorphism of schemes.** -/
theorem isPerfect_derivedPullback_scheme_iff {X Y : Scheme.{u}} (e : X ≅ Y)
    (E : DerivedCategory (OXMod.{u, u} Y.toLocallyRingedSpace.toRingedSpace)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect
        (X := X.toLocallyRingedSpace.toRingedSpace)
        ((derivedPullback (ringedSpaceIsoOfSchemeIso e).hom).obj E) ↔
      Stacks.Cohomology.PerfectComplexes.IsPerfect
        (X := Y.toLocallyRingedSpace.toRingedSpace) E :=
  isPerfect_derivedPullback_iff (ringedSpaceIsoOfSchemeIso e) E

end Stacks.Cohomology.TransportAlongIso

end
