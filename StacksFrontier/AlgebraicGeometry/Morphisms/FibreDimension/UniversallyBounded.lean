module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank

/-!
# Universally bounded fibres

An integer bounds the degrees of the fibres of a morphism of schemes when every fibre is a finite
locally free scheme over the corresponding residue field of degree at most that integer. The
fibres are *universally bounded* when such an integer exists.

## Main definitions

* `AlgebraicGeometry.BoundsFiberDegrees` says that an integer bounds the degrees of all fibres of
  a morphism.
* `AlgebraicGeometry.HasUniversallyBoundedFibers` says that the degrees of the fibres admit a
  common bound.

## Main results

* `AlgebraicGeometry.hasUniversallyBoundedFibers_of_boundsFiberDegrees`: a common integer bound
  on the degrees of the fibres makes those fibres universally bounded.

## Implementation notes

The degree of a finite scheme over a field is the rank of its structure morphism as a finite
locally free morphism, `Stacks.Morphisms.IsFiniteLocallyFreeOfRank`. A bound therefore asks for a
natural-number rank whose coercion to the integers is at most the given integer. The
nonnegativity condition on the integer in the source is unnecessary: the given integer itself is
the bound required by the definition.

## References

* [Stacks Project, Tag 03J4](https://stacks.math.columbia.edu/tag/03J4)
* [Stacks Project, Tag 03J5](https://stacks.math.columbia.edu/tag/03J5)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An integer bounds the degrees of the fibres of `f` if each fibre is finite locally free of
some rank no greater than that integer. -/
@[stacks 03J4 "part (1)"]
public abbrev BoundsFiberDegrees {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℤ) : Prop :=
  ∀ y : Y, ∃ r : ℕ, (r : ℤ) ≤ n ∧
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField y) r

/-- The fibres of `f` are universally bounded if their degrees have a common integer bound. -/
@[stacks 03J4 "part (2)"]
public abbrev HasUniversallyBoundedFibers {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ n : ℤ, BoundsFiberDegrees f n

/-- A common integer bound on the degrees of the fibres makes those fibres universally
bounded. -/
@[stacks 03J5 "universally_bounded"]
public lemma hasUniversallyBoundedFibers_of_boundsFiberDegrees {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℤ) (h : BoundsFiberDegrees f n) : HasUniversallyBoundedFibers f :=
  ⟨n, h⟩

end AlgebraicGeometry

end
