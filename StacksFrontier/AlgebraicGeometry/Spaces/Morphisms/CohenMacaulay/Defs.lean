module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.CohenMacaulayFiber
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.AtAPoint

/-!
# Cohen–Macaulay morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is *Cohen–Macaulay at* a point of its
source when it is flat there and the local ring of its fibre is Noetherian and
Cohen–Macaulay in pointed étale scheme charts at that point; it is *Cohen–Macaulay* when
this holds at every point of its source.

## Main definitions

* `AlgebraicGeometry.Space.IsCohenMacaulayAt` is Cohen–Macaulayness at a point of the
  source.
* `AlgebraicGeometry.Space.IsCohenMacaulay` is Cohen–Macaulayness of the morphism.

## References

* [Stacks Project, Tag 0E0V](https://stacks.math.columbia.edu/tag/0E0V)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- A morphism of algebraic spaces over `S` is *Cohen–Macaulay at* a point `x` of its source
when it is flat at `x` and the local ring of its fibre is Noetherian and Cohen–Macaulay in every
pointed étale scheme chart at `x`. -/
@[stacks 0E0V "part (1): at a point"]
abbrev IsCohenMacaulayAt (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (x : points B S hS X) : Prop :=
  IsFlatAt B S hS f x ∧
    HoldsOnEveryEtaleChartAtPoint B S hS (@HasCohenMacaulayFiberLocalRing.{u}) f x

/-- A morphism of algebraic spaces over `S` is *Cohen–Macaulay* when it is Cohen–Macaulay at
every point of its source. -/
@[stacks 0E0V "part (2): morphism"]
abbrev IsCohenMacaulay (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop :=
  ∀ x : points B S hS X, IsCohenMacaulayAt B S hS f x

end AlgebraicGeometry.Space

end
