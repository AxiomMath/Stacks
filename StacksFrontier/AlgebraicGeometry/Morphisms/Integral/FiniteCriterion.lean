module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite morphisms are the integral morphisms locally of finite type

A finite morphism of schemes is integral, and an integral morphism which is locally of finite
type is finite. Mathlib proves the resulting equivalence, so it is recorded against the library
declaration; the direction producing finiteness is restated here as a lemma that can be applied
directly to a morphism known to be integral and locally of finite type.

## Main results

* `AlgebraicGeometry.IsFinite.of_isIntegralHom_of_locallyOfFiniteType` says that an integral
  morphism which is locally of finite type is finite.

## References

* [Stacks Project, Tag 01WJ](https://stacks.math.columbia.edu/tag/01WJ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

add_to_stacks 01WJ "A finite morphism is integral, and an integral morphism which is locally
  of finite type is finite." AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType
add_to_ega "II 6.1.1" AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- An integral morphism of schemes which is locally of finite type is finite. -/
@[stacks 01WJ "only the second assertion, that an integral morphism which is locally of finite
  type is finite; the first assertion, that a finite morphism is integral, is not stated here and
  is part of `AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType`",
  ega "II 6.1.1" "partial"]
theorem IsFinite.of_isIntegralHom_of_locallyOfFiniteType
    [IsIntegralHom f] [LocallyOfFiniteType f] : IsFinite f :=
  (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mpr ⟨‹_›, ‹_›⟩

end AlgebraicGeometry

end
