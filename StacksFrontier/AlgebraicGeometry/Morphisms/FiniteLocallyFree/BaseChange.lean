module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Basic

/-!
# Base change of finite locally free morphisms

A finite locally free morphism of schemes stays finite locally free after an arbitrary base
change.

## Main results

* `Stacks.Morphisms.isFiniteLocallyFree_isStableUnderBaseChange`: finite locally free morphisms
  of schemes are stable under arbitrary base change.

## Implementation notes

The statement is Mathlib's categorical predicate
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange`, so it applies to every pullback
square and not only to the chosen pullback. The proof reads the property as finiteness, flatness
and local finite presentation, each of which Mathlib already knows to be stable under base
change.

## References

* [Stacks Project, Tag 02KD](https://stacks.math.columbia.edu/tag/02KD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Morphisms

/-- **Stacks Project, Tag 02KD.** A base change of a finite locally free morphism is finite
locally free. -/
@[stacks 02KD]
instance isFiniteLocallyFree_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (@IsFiniteLocallyFree : MorphismProperty Scheme.{u}) := by
  refine ⟨?_⟩
  intro X Y Y' S f g f' g' hpb hg
  obtain ⟨hfin, hflat, hlfp⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).mp hg
  refine (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g').mpr
    ⟨?_, ?_, ?_⟩
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hfin
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hflat
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hlfp

end Stacks.Morphisms

end
