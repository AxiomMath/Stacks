module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of finite type are stable under base change

A morphism of schemes is of finite type when it is locally of finite type and
quasi-compact, which is the morphism property
`@AlgebraicGeometry.LocallyOfFiniteType ⊓ @AlgebraicGeometry.QuasiCompact` already used for
this notion elsewhere in the library. Both conjuncts are preserved by arbitrary base change,
by `AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange` and
`AlgebraicGeometry.quasiCompact_isStableUnderBaseChange`, so the conjunction is too, by
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange.inf`. This is the entry of the
base-change list for being of finite type; the entry for being *locally* of finite type is
the first of those two conjuncts and is recorded in
`StacksFrontier.AlgebraicGeometry.Spaces.Representable.BaseChange`.

## Main results

* `AlgebraicGeometry.Space.finiteType_isStableUnderBaseChange`: a morphism of schemes of
  finite type stays of finite type after arbitrary base change.

## References

* [Stacks Project, Tag 02WF](https://stacks.math.columbia.edu/tag/02WF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

/-- Morphisms of schemes of finite type remain of finite type after arbitrary base
change. -/
@[stacks 02WF "of_finite_type"]
public instance finiteType_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      ((@LocallyOfFiniteType : MorphismProperty Scheme.{u}) ⊓ @QuasiCompact) := .inf

end AlgebraicGeometry.Space

end
