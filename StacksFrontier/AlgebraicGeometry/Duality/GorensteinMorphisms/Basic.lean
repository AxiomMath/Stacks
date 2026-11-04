module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.Dualizing.Gorenstein

/-!
# Gorenstein morphisms

A morphism of schemes with locally Noetherian fibres is Gorenstein at a point when it is flat
there and the local ring of the corresponding fibre is Gorenstein. It is a Gorenstein morphism
when this holds at every point.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsGorensteinAt`: Gorensteinness of a morphism at a point.
* `AlgebraicGeometry.Scheme.Hom.IsGorenstein`: Gorensteinness of a morphism at every point of the
  source.

## References

* [Stacks Project, Tag 0C04](https://stacks.math.columbia.edu/tag/0C04)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A scheme morphism with locally Noetherian fibres is Gorenstein at `x` if it
is flat at `x` and the local ring of the fibre over `f x` is Gorenstein. -/
@[stacks 0C04 "part (1)"]
public abbrev IsGorensteinAt {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) (x : X) : Prop :=
  letI := hf (f x)
  IsFlatAt f.toLRSHom.toShHom x ∧
    Dualizing.IsGorensteinLocalRing
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x))

/-- A scheme morphism with locally Noetherian fibres is Gorenstein when it is
Gorenstein at every point of the source. -/
@[stacks 0C04 "part (2)"]
public abbrev IsGorenstein {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) : Prop :=
  ∀ x : X, IsGorensteinAt f hf x

end AlgebraicGeometry.Scheme.Hom
