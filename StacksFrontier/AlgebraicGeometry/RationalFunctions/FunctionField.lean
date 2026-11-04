module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.FunctionField
public import StacksFrontier.AlgebraicGeometry.RationalFunctions.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The function field of an integral scheme

The *function field*, or *field of rational functions*, of an integral scheme `X` is the ring
`R(X)` of rational functions on `X`, which is a field because `X` is integral.

## Main definitions

* `AlgebraicGeometry.Scheme.functionFieldOfRationalFunctions`: the function field `R(X)` of an
  integral scheme `X`.

## Implementation notes

The ring of rational functions `AlgebraicGeometry.Scheme.rationalFunctions` (Stacks 01RT) and
`Stacks.Chow.rationalFunctions` are both the rational maps from `X` to the affine line over the
integers, spelled the same way, so they are the same type by unfolding reducible definitions.
The ring structure on it is `Stacks.Chow.rationalFunctionsRing` (Stacks 01RU), and the field
structure on an integral scheme is the `Field` instance next to
`Stacks.Chow.isField_rationalFunctions` (Stacks 01RV), which identifies `R(X)` with the stalk
`AlgebraicGeometry.Scheme.functionField` at the generic point through
`Stacks.Chow.rationalFunctionsEquivFunctionField`. The function field is defined as an
abbreviation, so it carries that field structure.

## References

* [Stacks Project, Tag 01RW](https://stacks.math.columbia.edu/tag/01RW)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- The *function field*, or *field of rational functions*, of an integral scheme `X`: the ring
`R(X)` of rational functions on `X`, which is a field because `X` is integral. -/
@[stacks 01RW]
abbrev functionFieldOfRationalFunctions (X : Scheme.{u}) [IsIntegral X] : Type u :=
  X.rationalFunctions

end AlgebraicGeometry.Scheme
