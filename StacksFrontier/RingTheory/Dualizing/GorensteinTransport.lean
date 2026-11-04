module

public import StacksFrontier.AlgebraicGeometry.Duality.Dualizing
public import StacksFrontier.RingTheory.Dualizing.FlatLocalGorenstein

/-!
# Gorensteinness of a Noetherian local ring is an isomorphism invariant

`Dualizing.IsGorensteinLocalRing` is defined by a condition on the derived category of modules
over the ring, so it is not immediately visible that two isomorphic Noetherian local rings are
Gorenstein together. This file records that they are.

One direction is `Dualizing.isGorensteinLocalRing_of_ringEquiv`: an isomorphism `A ≃+* B` is a
flat local homomorphism, so the criterion of Tag 0BJL applies to it. Applying that to the
isomorphism and to its inverse gives both implications.

## Main results

* `Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff` — isomorphic Noetherian local rings are
  Gorenstein together.

## Implementation notes

The two rings are taken in the same universe, which is what every use of the equivalence needs.
The descent step it is built from, `Dualizing.isGorensteinLocalRing_of_ringEquiv`, is stated for
two independent universes, and a use that crosses universes should name that lemma directly.

## References

* [Stacks Project, Tag 0DW7](https://stacks.math.columbia.edu/tag/0DW7)
* [Stacks Project, Tag 0BJL](https://stacks.math.columbia.edu/tag/0BJL)
-/

@[expose] public section

universe u

namespace Stacks.Duality

/-- **Isomorphic Noetherian local rings are Gorenstein together.** -/
public theorem isGorensteinLocalRing_ringEquiv_iff {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) :
    Dualizing.IsGorensteinLocalRing A ↔ Dualizing.IsGorensteinLocalRing B :=
  ⟨Dualizing.isGorensteinLocalRing_of_ringEquiv e.symm,
    Dualizing.isGorensteinLocalRing_of_ringEquiv e⟩

end Stacks.Duality
