module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import StacksCore.Tactic.StacksAttribute

/-!
# Further entries of the base-change list

Three more properties of morphisms of schemes that are preserved by arbitrary base change:
being locally of finite type, being quasi-compact, and being universally submersive. Each
of the three is a single existing result, so each is adopted rather than restated.

Being locally of finite type is `AlgebraicGeometry.LocallyOfFiniteType` and its stability is
`AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange`; quasi-compactness is
`AlgebraicGeometry.QuasiCompact` and its stability is
`AlgebraicGeometry.quasiCompact_isStableUnderBaseChange`. Universal submersiveness is the
universal closure of the property that the underlying continuous map be a quotient map, and
the universal closure of any morphism property is stable under base change by
`CategoryTheory.MorphismProperty.universally_isStableUnderBaseChange`.

## References

* [Stacks Project, Tag 02WF](https://stacks.math.columbia.edu/tag/02WF)
-/

@[expose] public section

add_to_stacks 02WF "quasi_compact" AlgebraicGeometry.quasiCompact_isStableUnderBaseChange

add_to_stacks 02WF "universally_submersive"
  CategoryTheory.MorphismProperty.universally_isStableUnderBaseChange

end
