module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# Points in a fibre of a cartesian diagram of algebraic spaces

Fix a scheme `S`. A cartesian square of algebraic spaces over `S` consists of four presheaves
on the big fppf site of `S`, each an algebraic space, together with four morphisms making the
square cartesian. Two points of its lower-left and upper-right corners lying over the same
point of the lower-right corner then determine a subset of the points of the upper-left
corner: those mapping to both of them.

## Main definitions

* `AlgebraicGeometry.Space.PointsFibresDiagram` is a cartesian square of algebraic spaces.
* `AlgebraicGeometry.Space.fibrePoints` is the set of points of the upper-left corner lying
  over two prescribed points of the lower-left and upper-right corners.

## References

* [Stacks Project, Tag 0AC1](https://stacks.math.columbia.edu/tag/0AC1)
* [Stacks Project, Tag 0AC2](https://stacks.math.columbia.edu/tag/0AC2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A cartesian diagram of algebraic spaces `W → Z`, `W → X`, `X → Y` and `Z → Y` over `S`. -/
@[stacks 0AC1]
structure PointsFibresDiagram (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) where
  /-- The upper left corner of the square. -/
  W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The lower left corner of the square. -/
  Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The upper right corner of the square. -/
  X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The lower right corner of the square. -/
  Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The upper left corner is an algebraic space. -/
  W_isAlgebraicSpace : IsAlgebraicSpace B S hS W
  /-- The lower left corner is an algebraic space. -/
  Z_isAlgebraicSpace : IsAlgebraicSpace B S hS Z
  /-- The upper right corner is an algebraic space. -/
  X_isAlgebraicSpace : IsAlgebraicSpace B S hS X
  /-- The lower right corner is an algebraic space. -/
  Y_isAlgebraicSpace : IsAlgebraicSpace B S hS Y
  /-- The left vertical morphism. -/
  q : W ⟶ Z
  /-- The upper horizontal morphism. -/
  p : W ⟶ X
  /-- The right vertical morphism. -/
  f : X ⟶ Y
  /-- The lower horizontal morphism. -/
  g : Z ⟶ Y
  /-- The displayed square is cartesian. -/
  isPullback : IsPullback p q f g

/-- The points of `W` mapping to the specified points `x` of `X` and `z` of `Z`, which have the
same image in `Y`, in a cartesian diagram. -/
@[stacks 0AC2]
def fibrePoints {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : PointsFibresDiagram B S hS) (x : points B S hS D.X) (z : points B S hS D.Z)
    (_h : pointsMap B S hS D.X D.f x = pointsMap B S hS D.Z D.g z) :
    Set (points B S hS D.W) :=
  {w | pointsMap B S hS D.W D.p w = x ∧ pointsMap B S hS D.W D.q w = z}

end AlgebraicGeometry.Space

end
