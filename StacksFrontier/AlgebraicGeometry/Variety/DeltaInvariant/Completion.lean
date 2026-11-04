module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.KrullDimension.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing
public import StacksFrontier.RingTheory.Nagata.Defs

/-!
# Properties of the completion of a one-dimensional Nagata local ring

The completion of a reduced one-dimensional Nagata local ring at its maximal ideal is again
reduced, Nagata, local, and one-dimensional.

## Main results

* `IsLocalRing.isReduced_adicCompletion_maximalIdeal_of_isNagataRing` gives reducedness of the
  completion.
* `IsLocalRing.isNagataRing_adicCompletion_maximalIdeal` gives the Nagata property of the
  completion of a Noetherian local ring.
* `AdicCompletion.isLocalRing_of_fg` gives locality of the completion.
* `IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal` says that completion preserves Krull
  dimension.

Together with `AdicCompletion.isNoetherianRing` and `AdicCompletion.isAdicComplete_of_fg` these
say that the completion of a reduced one-dimensional Nagata local ring is a reduced Noetherian
complete local ring of dimension one.

## References

* [Stacks Project, Tag 0C3V](https://stacks.math.columbia.edu/tag/0C3V)
* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
-/

@[expose] public section

add_to_stacks 0C3V "completion_properties" AdicCompletion.isLocalRing_of_fg
add_to_sga "3 VIIB 0.1.1" "special case" AdicCompletion.isLocalRing_of_fg
add_to_sga "3 X 4.0" "partial" AdicCompletion.isLocalRing_of_fg
add_to_ega "IV 8.11.4" "Â is a local ring" AdicCompletion.isLocalRing_of_fg

add_to_stacks 0C1R "completed_local_ring" AdicCompletion.isNoetherianRing
add_to_stacks 0C1R "completed_local_ring" AdicCompletion.isLocalRing_of_fg
add_to_stacks 0C1R "completed_local_ring" AdicCompletion.isAdicComplete_of_fg
add_to_ega "0 7.2.12" "special case" AdicCompletion.isAdicComplete_of_fg

namespace IsLocalRing

open IsLocalRing

/-- The maximal-ideal-adic completion of a reduced Nagata local ring is reduced. -/
@[stacks 0C3V "completion_properties", ega "IV 7.6.1" "more general"]
public theorem isReduced_adicCompletion_maximalIdeal_of_isNagataRing
    {A : Type*} [CommRing A] [IsLocalRing A] [IsReduced A]
    (hA : IsNagataRing A) : IsReduced (AdicCompletion (maximalIdeal A) A) := by
  let : IsNoetherianRing A := hA.1
  exact ((reducedness_and_adicCompletion.{_, 0} A).2.2 hA).mp ‹IsReduced A›

/-- The maximal-ideal-adic completion of a Noetherian local ring is a Nagata ring. -/
@[stacks 0C3V "completion_properties"]
public theorem isNagataRing_adicCompletion_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    IsNagataRing (AdicCompletion (maximalIdeal A) A) :=
  IsNagataRing.of_isPrecomplete_maximalIdeal

/-- Completion of a Noetherian local ring at its maximal ideal preserves Krull dimension. -/
@[stacks 0C3V "completion_properties", ega "IV 7.3.19" "dim(Â) = 1"]
public theorem ringKrullDim_adicCompletion_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    ringKrullDim (AdicCompletion (maximalIdeal A) A) = ringKrullDim A :=
  (_root_.ringKrullDim_adicCompletion_maximalIdeal (A := A)).symm

end IsLocalRing

add_to_stacks 0C1R "completed_local_ring"
  IsLocalRing.isReduced_adicCompletion_maximalIdeal_of_isNagataRing
add_to_stacks 0C1R "completed_local_ring"
  IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal
