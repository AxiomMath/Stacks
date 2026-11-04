module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.RingHomProperty

/-!
# Open immersions are syntomic

Every open immersion of schemes is syntomic.

## Main results

* `AlgebraicGeometry.syntomic_of_isOpenImmersion`: an open immersion is syntomic.

## References

* [Stacks Project, Tag 01UJ](https://stacks.math.columbia.edu/tag/01UJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Every open immersion of schemes is syntomic. -/
@[stacks 01UJ]
lemma syntomic_of_isOpenImmersion {X S : Scheme.{u}} (f : X ⟶ S)
    [IsOpenImmersion f] : Syntomic f :=
  HasRingHomProperty.of_isOpenImmersion (P := @Syntomic) (Q := @RingHom.Syntomic) (f := f)
    RingHom.syntomic_containsIdentities

end AlgebraicGeometry
