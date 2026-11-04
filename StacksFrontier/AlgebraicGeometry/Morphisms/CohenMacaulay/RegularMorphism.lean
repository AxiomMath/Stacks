module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Regular
public import StacksCore.Tactic.StacksAttribute

/-!
# Regular morphisms of schemes

A morphism of schemes is regular at a point when it is flat there and its fibre over the image
point is geometrically regular at the corresponding point. It is regular if this holds at every
point.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsRegularAt` is regularity of a morphism at a source point.
* `AlgebraicGeometry.Scheme.Hom.IsRegular` is regularity at every source point.

## Implementation notes

The point of the fibre corresponding to `x` is `f.asFiber x`; geometric regularity is taken
relative to the canonical morphism from the fibre to the spectrum of the residue field of
`f x`. The source assumes locally Noetherian fibres as context. As with geometric regularity
itself, the predicates make sense without that assumption, which clients can impose separately.
Both definitions are abbreviations, so clients can use the flatness and geometric-regularity
conjuncts, and quantify over source points, without a separate unfolding API.

Both predicates are properties of a *morphism* and live in the `AlgebraicGeometry.Scheme.Hom`
namespace, so that they read as `f.IsRegularAt x` and `f.IsRegular`. They are not to be
confused with the regularity of a *scheme*.

## References

* [Stacks Project, Tag 07R7](https://stacks.math.columbia.edu/tag/07R7)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **Stacks Project, Tag 07R7, part (1).** Regularity of a scheme morphism at a point. -/
@[stacks 07R7 "part (1)", ega "IV 6.8.1"]
public abbrev IsRegularAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : Prop :=
  IsFlatAt f.toLRSHom.toShHom x ∧
    IsGeometricallyRegularAt (f.fiberToSpecResidueField (f x)) (f.asFiber x)

/-- **Stacks Project, Tag 07R7, part (2).** Regularity at every source point. -/
@[stacks 07R7 "part (2)", ega "IV 6.8.1"]
public abbrev IsRegular {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop := ∀ x : X, IsRegularAt f x

end AlgebraicGeometry.Scheme.Hom
