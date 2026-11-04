module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# Flat and surjective morphisms of algebraic spaces

A morphism of algebraic spaces over `S` is *flat* when the morphism of schemes underlying every
commuting square of étale scheme charts of it is flat. A morphism of presheaves on the big fppf
site over `S` is *surjective* when the induced map on the underlying point sets `|X| → |Y|` is
surjective.

## Main definitions

* `AlgebraicGeometry.Space.IsFlat`: flatness of a morphism of algebraic spaces, tested on every
  pair of compatible étale scheme charts.
* `AlgebraicGeometry.Space.IsSurjective`: surjectivity of a morphism of algebraic spaces, namely
  surjectivity of its map on points.

## References

* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- A morphism of algebraic spaces over `S` is *flat* when the morphism of schemes underlying every
commuting square of étale scheme charts of it is flat. -/
@[stacks 03ML "part (1)"]
abbrev IsFlat (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) : Prop :=
  HoldsOnEveryEtaleChart B S hS
    (@_root_.AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) f

/-- A morphism of algebraic spaces over `S` is *surjective* when the induced map `|X| → |Y|` on
their sets of points is surjective. -/
@[stacks 03ME]
abbrev IsSurjective (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop :=
  Function.Surjective (pointsMap B S hS X f)

end AlgebraicGeometry.Space

end
