module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute

/-!
# A subset of the prime spectrum determined by two ideals

For ideals `I` and `J` of a commutative ring `A`, the algebraization arguments of Stacks
chapter 52 single out the primes `p` with the property that every specialization of `p` which
lies in `V(I)` already lies in `V(J)`. Equivalently, `V(p) ∩ V(I) ⊆ V(J) ∩ V(I)`. This is the
subset denoted `T` in Stacks Project, Tag 0EFG, and it is the index set along which the
cohomological dimension bounds of that chapter are checked.

## Main definitions

* `Stacks.Algebraization.associatedSubset` — the set of primes `p` such that
  `V(p) ∩ V(I) ⊆ V(J) ∩ V(I)`.

## Implementation notes

The finiteness hypotheses carried by the surrounding section of the Stacks source are not
needed to form this subset, so the definition is made for an arbitrary commutative ring. The
containment is stated between the closed sets `PrimeSpectrum.zeroLocus` rather than between
sets of primes, which is the form in which the chapter's topological lemmas apply to it.

## References

* [Stacks Project, Tag 0EFG](https://stacks.math.columbia.edu/tag/0EFG)
-/

@[expose] public section

namespace Stacks.Algebraization

variable {A : Type*} [CommRing A]

/-- The primes whose specializations in `V(I)` all belong to `V(J) ∩ V(I)`.

This is the subset denoted by `T` in Stacks Project, Tag 0EFG. -/
@[stacks 0EFG]
def associatedSubset (I J : Ideal A) : Set (PrimeSpectrum A) :=
  {p | PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ⊆
    PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)}

end Stacks.Algebraization
