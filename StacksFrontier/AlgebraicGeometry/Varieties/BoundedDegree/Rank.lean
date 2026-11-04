module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
/-!
# Composing a finite locally free morphism of a given rank with an isomorphism

Composing on either side with an isomorphism of schemes does not change the rank of a finite
locally free morphism.

## Main results

* `Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isIso_comp` and
  `Stacks.Morphisms.IsFiniteLocallyFreeOfRank.comp_isIso`: precomposing, respectively
  postcomposing, with an isomorphism preserves finite local freeness of rank `r`.

## Implementation notes

Both are instances of the fact that `Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property`
respects isomorphisms, read through
`CategoryTheory.MorphismProperty.cancel_left_of_respectsIso` and
`CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`.  They are stated as transports of
the typeclass, which is the form the consumers of a rank bound need.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Morphisms

/-- Precomposing a morphism that is finite locally free of rank `r` with an isomorphism leaves
it finite locally free of rank `r`. -/
theorem IsFiniteLocallyFreeOfRank.isIso_comp {X X' S : Scheme.{u}} (e : X' ⟶ X) [IsIso e]
    (f : X ⟶ S) (r : ℕ) [h : IsFiniteLocallyFreeOfRank f r] :
    IsFiniteLocallyFreeOfRank (e ≫ f) r :=
  ((IsFiniteLocallyFreeOfRank.property.{u} r).cancel_left_of_respectsIso e f).mpr h

/-- Postcomposing a morphism that is finite locally free of rank `r` with an isomorphism leaves
it finite locally free of rank `r`. -/
theorem IsFiniteLocallyFreeOfRank.comp_isIso {X S S' : Scheme.{u}} (f : X ⟶ S) (e : S ⟶ S')
    [IsIso e] (r : ℕ) [h : IsFiniteLocallyFreeOfRank f r] :
    IsFiniteLocallyFreeOfRank (f ≫ e) r :=
  ((IsFiniteLocallyFreeOfRank.property.{u} r).cancel_right_of_respectsIso f e).mpr h

end Stacks.Morphisms

end
