module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Thickenings

/-!
# The inclusion of a thickening is a universal homeomorphism

A thickening `i : X ⟶ X'` is a closed immersion which is surjective on points, so it is a
homeomorphism on the underlying topological spaces. Both conditions are stable under base
change, so the same holds after any base change: `i` is a universal homeomorphism.

This is the topological input for comparing a property of the two vertical morphisms in a
commutative square whose horizontal morphisms are thickenings: applying the result to the
source and to the target thickening makes both inclusions universal homeomorphisms, and the
maps of the square itself are not needed for that.

## Main results

* `Stacks.Thickenings.IsThickening.universalHomeomorphism`: the inclusion of a thickening is a
  universal homeomorphism.

## References

* [Stacks Project, Tag 04DD](https://stacks.math.columbia.edu/tag/04DD)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace Stacks.Thickenings

universe u

namespace IsThickening

/-- The inclusion of a thickening is a universal homeomorphism: every base change of it is a
closed immersion and surjective, hence a closed embedding which is bijective. -/
lemma universalHomeomorphism {X X' : Scheme.{u}} {i : X ⟶ X'}
    (hi : IsThickening i) : UniversalHomeomorphism i := by
  rw [universalHomeomorphism_iff]
  have : (topologically @IsHomeomorph).RespectsIso :=
    topologically_respectsIso _ (fun e => e.isHomeomorph) fun _ _ hf hg => hg.comp hf
  refine universally_mk' _ i fun f _ => ?_
  have : IsClosedImmersion i := hi.1
  have : Surjective i := ⟨hi.2⟩
  have hg : IsClosedImmersion (pullback.fst f i) := inferInstance
  change IsHomeomorph (pullback.fst f i).base
  exact isHomeomorph_iff_continuous_isClosedMap_bijective.2 ⟨(pullback.fst f i).continuous,
    hg.isClosedEmbedding.isClosedMap, hg.isClosedEmbedding.injective,
    (pullback.fst f i).surjective⟩

end IsThickening

end Stacks.Thickenings

end
