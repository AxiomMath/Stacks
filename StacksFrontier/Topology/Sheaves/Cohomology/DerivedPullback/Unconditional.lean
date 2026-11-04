module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# The derived pullback on a ringed space, with no hypothesis left over

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.KFlatResolvingDatum` instantiates the
resolving-datum criterion of Tag 079W at the K-flat complexes and proves everything that follows
from the datum, under the single hypothesis
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.PullbackInvertsQuasiIso f
  (Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Y)`.
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional` proves that
hypothesis, as `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackInvertsQuasiIso_isKFlat`,
and records the resulting existence statement as the instance
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.hasLeftDerivedFunctor_pullbackOnHomotopy`.

This file discharges the hypothesis in the two remaining consequences and records Tag 06YJ.

## Main results

* `Stacks.Cohomology.KFlatDerivedPullback.comp_isLeftDerivedFunctor`: **absoluteness of `Lf^*`**,
  for every morphism of ringed spaces, as an instance. `Functor.HasLeftDerivedFunctor` does not
  imply it, so it cannot be recovered from the existence instance alone.
* `Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat`: **a
  K-flat complex computes `Lf^*`**, for every morphism of ringed spaces: on it the canonical
  comparison `Lf^* K ⟶ f^* K` is invertible.

## Implementation notes

The existence statement `Lf^*` needs is the instance
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.hasLeftDerivedFunctor_pullbackOnHomotopy`;
`Lf^*` itself and its comparison are
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` and
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison`; and the adjunction
is `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction`. None of them is
restated here: the Tag 06YJ clauses they realize are attached to them by `add_to_stacks` below.

The abbreviation `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` is stated
in a section with `[(pullbackOnHomotopy f).HasLeftDerivedFunctor (HomotopyCategory.quasiIso …)]`
in scope. `Functor.HasLeftDerivedFunctor` is a `Prop`, so the binder is proof-irrelevant: every
instance of it gives the same functor, and
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.hasLeftDerivedFunctor_pullbackOnHomotopy`
supplies one for every morphism of ringed spaces. So
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f` and
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f` elaborate here
with no input beyond `f`, which is the hypothesis shape of Tag 06YJ.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.KFlatDerivedPullback

universe w₁ w₂ u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **Absoluteness of `Lf^*`**, for an arbitrary morphism of ringed spaces: the derived pullback
stays a left derived functor after composing with the derived pushforward.

This is strictly stronger than `Functor.HasLeftDerivedFunctor` for `f^*`, which does not imply
it, so it is seated as an instance rather than left for a consumer to rederive. -/
instance comp_isLeftDerivedFunctor :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f ⋙
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f)).inv ≫
        Functor.whiskerRight
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f)
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :=
  comp_isLeftDerivedFunctor_of_kFlat f
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackInvertsQuasiIso_isKFlat f)

/-- **A K-flat complex computes the derived pullback**: on it the canonical comparison
`Lf^* K ⟶ f^* K` is invertible.  This is the clause of Tag 06YJ that says the construction
agrees with degreewise pullback where degreewise pullback is already derived, and it holds for
an arbitrary morphism of ringed spaces: the K-flat complexes are a resolving datum for `f^*`,
and the comparison of a left derived functor is invertible on its resolving class.

The two models of the derived categories are binders rather than the file's pinned
`HasDerivedCategory.standard`: every ingredient of the proof is model-free. -/
@[stacks 06YJ "computation on K-flat complexes"]
theorem isIso_derivedPullbackComparison_app_of_kFlat
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) (hK : KFlatComplex Y K) :
    IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ)).obj K)) :=
  LeftDerivedByResolutions.isIso_app_of_resolutions
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    (IsKFlat Y) (hasResolutions_isKFlat Y)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy f)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackInvertsQuasiIso_isKFlat f)
      DerivedCategory.Qh
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f) _ hK

end

end Stacks.Cohomology.KFlatDerivedPullback

-- Tag 06YJ's derived pullback functor and its canonical comparison are
-- `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` and
-- `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison`, available for
-- every morphism of ringed spaces by
-- `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.hasLeftDerivedFunctor_pullbackOnHomotopy`.
add_to_stacks 06YJ "the derived pullback functor"
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback

add_to_stacks 06YJ "canonical comparison"
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison

end
