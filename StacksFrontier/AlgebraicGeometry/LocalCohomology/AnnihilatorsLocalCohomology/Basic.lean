module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import StacksFrontier.RingTheory.LocalCohomology.SectionsWithSupport
public import StacksCore.Tactic.StacksAttribute

/-!
# Depth of a bounded-below complex along an ideal

The depth of a bounded-below complex with respect to an ideal is the first degree in which its
local cohomology does not vanish, or infinity if all of its local cohomology vanishes.

## Main definitions

* `DerivedCategory.Plus.depth` is the depth of a bounded-below derived object with respect to an
  ideal.

## Implementation notes

The value lies in `WithTop ℤ`, the integers with infinity; the infimum of the degrees of nonzero
local cohomology is infinity exactly when that set is empty. A bounded-below derived object
suffices for this definition: neither finiteness of cohomology nor Noetherianity is needed. For a
local ring the depth is the specialization of this to the maximal ideal. The construction is an
abbreviation so that downstream statements can use the order API for the infimum directly.

Note that this `depth` is the depth of a derived object, and is placed in the
`DerivedCategory.Plus` namespace to distinguish it from `Module.depth`, the depth of a module
along an ideal.

## References

* [Stacks Project, Tag 0EHY](https://stacks.math.columbia.edu/tag/0EHY)
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace DerivedCategory.Plus

/-- The `I`-depth of a bounded-below derived object: the first degree of nonzero local
cohomology, or infinity if local cohomology vanishes throughout. -/
@[stacks 0EHY]
noncomputable abbrev depth (A : Type u) [CommRing A]
    (I : Ideal A) (K : DerivedCategory.Plus (ModuleCat.{max u v} A)) : WithTop ℤ :=
  sInf ((fun i : ℤ => (i : WithTop ℤ)) ''
    {i : ℤ |
      ¬ IsZero
        (Stacks.LocalCohomology.localCohomologyWithSupportInPlus
          A (PrimeSpectrum.zeroLocus (I : Set A)) K i)})

end DerivedCategory.Plus
