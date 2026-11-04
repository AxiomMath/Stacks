module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Right exactness of module pullback

Pullback of sheaves of modules along any morphism of ringed spaces,
`RingedSpaceModuleAdjunction.modulePullback`, is a left adjoint, hence preserves all colimits.
Consequently it is an exact functor, in the sense of membership of `CategoryTheory.exactFunctor`,
as soon as it preserves finite limits; in particular this holds for the pullback along the
inclusion of a closed subset.

## Main results

* `RingedSpaceModuleAdjunction.preservesColimits_modulePullback`: pullback of sheaves of modules
  along any morphism of ringed spaces preserves all colimits.
* `RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback`: it preserves finite
  colimits.
* `RingedSpaceModuleAdjunction.exactFunctor_modulePullback_of_preservesFiniteLimits`: module
  pullback is an exact functor as soon as it preserves finite limits.
* `Stacks.Cohomology.SupportedComplexes.pullbackExact_of_preservesFiniteLimits`: pullback of
  sheaves of modules along the inclusion of a closed subset is an exact functor as soon as it
  preserves finite limits.

## References

* [Stacks Project, Tag 0AEF](https://stacks.math.columbia.edu/tag/0AEF)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace RingedSpaceModuleAdjunction

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **Pullback of sheaves of modules along a morphism of ringed spaces preserves all colimits.** -/
@[sga "4 IV 13.6" "ringed spaces, u*"]
theorem preservesColimits_modulePullback : PreservesColimits (modulePullback f) :=
  (modulePullbackPushforwardAdjunction f).leftAdjoint_preservesColimits

/-- **Pullback of sheaves of modules along a morphism of ringed spaces is right exact**: it
preserves finite colimits. -/
theorem preservesFiniteColimits_modulePullback :
    PreservesFiniteColimits (modulePullback f) :=
  have := preservesColimits_modulePullback f
  inferInstance

/-- **Module pullback is an exact functor as soon as it is left exact**: if it preserves finite
limits, it belongs to `CategoryTheory.exactFunctor`. -/
theorem exactFunctor_modulePullback_of_preservesFiniteLimits
    (h : PreservesFiniteLimits (modulePullback f)) :
    exactFunctor (SheafOfModules.{u} (structureSheafRing Y))
      (SheafOfModules.{u} (structureSheafRing X)) (modulePullback f) :=
  ⟨h, preservesFiniteColimits_modulePullback f⟩

end RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.SupportedComplexes

open RingedSpaceModuleAdjunction

/-- Pullback of sheaves of modules along the inclusion of a closed subset `Z` of `X` is an exact
functor as soon as it preserves finite limits. -/
theorem pullbackExact_of_preservesFiniteLimits (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (h : PreservesFiniteLimits (modulePullback (closedSubsetInclusion X Z))) :
    exactFunctor (SheafOfModules.{u} (structureSheafRing X))
      (SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z)))
      (modulePullback (closedSubsetInclusion X Z)) :=
  exactFunctor_modulePullback_of_preservesFiniteLimits _ h

end Stacks.Cohomology.SupportedComplexes

end
