module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Normal
public import StacksCore.Tactic.StacksAttribute

/-!
# Normal morphisms

A morphism of schemes is normal at a point when it is flat there and its fibre is geometrically
normal at the corresponding point. It is normal when it is normal at every point of its source.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsNormalAt` expresses normality of a morphism at a point.
* `AlgebraicGeometry.Scheme.Hom.IsNormal` expresses normality of a morphism at every point.

## Implementation notes

The point of the fibre is the canonical point `f.asFiber x`, and its structure morphism is
`f.fiberToSpecResidueField (f x)`. The source states these definitions in a context where all
fibres are locally Noetherian. The predicates themselves do not use that standing condition, so
it can be paired with them by applications, as in the source's subsequent locality results.
Both predicates are abbreviations so that the APIs for flatness and geometric normality apply
directly.

Both predicates are properties of a *morphism* and live in the `AlgebraicGeometry.Scheme.Hom`
namespace, so that they read as `f.IsNormalAt x` and `f.IsNormal`. They are not to be confused
with `AlgebraicGeometry.IsNormal`, the normality of a *scheme*.

## References

* [Stacks Project, Tag 0390](https://stacks.math.columbia.edu/tag/0390)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism of schemes is normal at `x` if it is flat at `x` and its fibre over the image
of `x` is geometrically normal at the point induced by `x`. -/
@[stacks 0390 "part (1)", ega "IV 6.8.1"]
public abbrev IsNormalAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : Prop :=
  IsFlatAt f.toLRSHom.toShHom x ∧
    IsGeometricallyNormalAt (f.fiberToSpecResidueField (f x)) (f.asFiber x)

/-- A morphism of schemes is normal if it is normal at every point of its source. -/
@[stacks 0390 "part (2)", ega "IV 6.8.1"]
public abbrev IsNormal {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop := ∀ x : X, IsNormalAt f x

end AlgebraicGeometry.Scheme.Hom
