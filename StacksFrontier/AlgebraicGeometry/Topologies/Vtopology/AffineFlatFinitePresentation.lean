module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Affine schemes flat and of finite presentation over a base

This records the standing condition on a scheme over a base that it is affine, and flat and of
finite presentation over that base. It is the hypothesis under which a family of schemes over
the limit of a cofiltered inverse system descends to a finite stage.

## Main definitions

* `AlgebraicGeometry.IsAffineFlatOfFinitePresentation` is that condition.

## Implementation notes

Finite presentation is spelled out as quasi-compactness, quasi-separatedness and local finite
presentation of the structure morphism, so that the three can be used as instances
individually; packaging them into `AlgebraicGeometry.FinitePresentation` is then immediate.

## References

* [Stacks Project, Tag 049N](https://stacks.math.columbia.edu/tag/049N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The condition defining affine schemes which are flat and of finite presentation over a base
scheme. -/
abbrev IsAffineFlatOfFinitePresentation {T : AlgebraicGeometry.Scheme.{u}}
    (X : Over T) : Prop :=
  AlgebraicGeometry.IsAffine X.left ∧
    AlgebraicGeometry.Flat X.hom ∧
    AlgebraicGeometry.QuasiCompact X.hom ∧
    AlgebraicGeometry.QuasiSeparated X.hom ∧
    AlgebraicGeometry.LocallyOfFinitePresentation X.hom

end AlgebraicGeometry
