module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.KrullDimension.SystemOfParameters.Defs

/-!
# Cohen--Macaulay local rings of a given dimension

A local ring is *Cohen--Macaulay of dimension `d`* when its Krull dimension is `d` and it
admits a system of `d` parameters which is a weakly regular sequence on the ring.

The source's condition that each parameter be a nonzerodivisor modulo its predecessors is
exactly `RingTheory.Sequence.IsWeaklyRegular`. A system of parameters is
`IsLocalRing.IsSystemOfParameters`: the ideal it generates has the maximal ideal as its
radical, and its length is the Krull dimension. The explicit length and dimension equalities
keep the named dimension `d` of the source. The predicate is an abbreviation, so the existing
system-of-parameters and regular-sequence APIs apply to it directly. Noetherianness is not
assumed, since none of the conditions needs it; the source applies the definition to
Noetherian local rings.

## Main definitions

* `IsLocalRing.IsCohenMacaulayOfDimension`: Cohen--Macaulayness with a specified finite
  dimension, in its regular-sequence formulation.

## References

* [Stacks Project, Tag 0285](https://stacks.math.columbia.edu/tag/0285)
-/

@[expose] public section

namespace IsLocalRing

/-- A local ring `A` is *Cohen--Macaulay of dimension `d`* if its Krull dimension is `d` and
there is a system of parameters `x₁, ..., x_d` such that every `xᵢ` is a nonzerodivisor on the
quotient by its predecessors. -/
@[stacks 0285]
abbrev IsCohenMacaulayOfDimension (A : Type*) [CommRing A] [IsLocalRing A] (d : ℕ) : Prop :=
  ringKrullDim A = d ∧ ∃ xs : List A, xs.length = d ∧
    IsLocalRing.IsSystemOfParameters xs ∧ RingTheory.Sequence.IsWeaklyRegular A xs

end IsLocalRing

end
