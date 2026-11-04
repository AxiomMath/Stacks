module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

/-!
# Binary products in the small étale site, and their preservation by base change

The small étale site of a scheme has a final object and fibre products (Tag 021D), hence all
finite limits — `AlgebraicGeometry.hasFiniteLimits_smallEtale` — and base change along a
morphism of the big étale site preserves them —
`AlgebraicGeometry.preservesFiniteLimits_smallEtaleBaseChange`. This file records the
binary-product shape of both, which is the form consumed when comparing a localization of the
site with a localization of its base change.

## Main results

* `AlgebraicGeometry.hasBinaryProducts_smallEtale` — the small étale site has binary products.
* `AlgebraicGeometry.preservesBinaryProducts_smallEtaleBaseChange` — small étale base change
  preserves binary products.

## Implementation notes

`AlgebraicGeometry.hasFiniteLimits_smallEtale` is registered as an instance where it is proved,
but reaching a single finite shape through it means searching through the terminal object and
fibre products, so the shapes actually used are registered individually here.

No `@[stacks]` attribute appears in this file. Tag 021D is the existence of fibre products and of
the final object, already attributed where it is proved; what is added here is the passage from
those two to the binary-product shape, which is Mathlib's and carries no tag of its own.

## References

* [Stacks Project, Tag 021D](https://stacks.math.columbia.edu/tag/021D)
* [Stacks Project, Tag 021I](https://stacks.math.columbia.edu/tag/021I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The small étale site has binary products. -/
public instance hasBinaryProducts_smallEtale (B : BigEtaleSite.{u}) (X : Scheme.{u})
    (hX : B.Contains X) : HasBinaryProducts (SmallEtale B X hX) :=
  (hasFiniteLimits_smallEtale B X hX).out (Discrete WalkingPair)

/-- Small étale base change preserves binary products. -/
public instance preservesBinaryProducts_smallEtaleBaseChange (B : BigEtaleSite.{u})
    {S T : B.Scheme} (f : T ⟶ S) :
    PreservesLimitsOfShape (Discrete WalkingPair) (smallEtaleBaseChange B f) :=
  inferInstance

end AlgebraicGeometry

end
