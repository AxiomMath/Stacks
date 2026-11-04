module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
public import StacksFrontier.Deformation.Groupoid.Basic

/-!
# Presentations by groupoids in functors

A presentation of a category cofibered in groupoids by a groupoid in functors.

## Main definitions

* `Presentation` is a presentation by a groupoid in functors.

## Implementation notes

The quotient is the Grothendieck construction of the evaluation functor, with
its canonical projection to `C`. An equivalence over `C` includes functors in
both directions and vertical unit and counit isomorphisms. Between categories
cofibered in groupoids, these functors preserve cocartesian arrows. The
abbreviation lets clients use the existing API for equivalences over a base
without unfolding a separate presentation structure.

## References

* [Stacks Project, Tag 06KX](https://stacks.math.columbia.edu/tag/06KX)
-/

@[expose] public section

namespace Deformation

/-! ### Presentations by groupoids in functors -/

section
open CategoryTheory

universe u v w u₁ v₁

/-- An equivalence over `C` from the quotient of `G` to a category over `C`.
When the latter is cofibered in groupoids, this is a presentation in the
sense of Stacks Project, Tag 06KX. -/
@[stacks 06KX]
public abbrev Presentation {C : Type u} [Category.{v} C] (G : GroupoidInFunctors.{u, v, w} C)
    {F : Type u₁} [Category.{v₁} F] (p : F ⥤ C) :=
  StacksRepresentableCFG.EquivalenceOver (Grothendieck.forget (evaluationFunctor G)) p

end

end Deformation
