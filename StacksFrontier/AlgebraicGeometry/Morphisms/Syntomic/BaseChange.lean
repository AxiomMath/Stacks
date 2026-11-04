module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.RingHomProperty
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Base change of syntomic morphisms

A syntomic morphism of schemes remains syntomic after arbitrary base change.

## Main results

* `AlgebraicGeometry.syntomic_isStableUnderBaseChange` states that syntomic morphisms of schemes
  are stable under arbitrary base change.

## Implementation notes

The result is expressed as an instance of Mathlib's categorical predicate
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange`, so it applies directly to every
pullback square, independently of a chosen pullback construction. It is deduced from base-change
stability of syntomicity for ring maps through
`AlgebraicGeometry.Syntomic.hasRingHomProperty`.

## References

* [Stacks Project, Tag 01UI](https://stacks.math.columbia.edu/tag/01UI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 01UI.** A base change of a syntomic morphism is syntomic. -/
@[stacks 01UI]
instance syntomic_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange (@Syntomic : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.syntomic_isStableUnderBaseChange

end AlgebraicGeometry
