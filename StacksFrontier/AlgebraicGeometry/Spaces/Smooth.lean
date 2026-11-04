module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# Smooth morphisms of algebraic spaces

Smoothness of morphisms of schemes is étale local on the source and target, stable under
base change and fppf local on the target, so by Tag 03MJ it transfers to morphisms of
algebraic spaces: a morphism of algebraic spaces over `S` is *smooth* when the scheme
morphism it induces in every commuting square of étale charts is smooth. It is *smooth at a
point* of its source when it is smooth on some open subspace containing that point.

## Main definitions

* `AlgebraicGeometry.Space.IsSmooth`: a morphism of algebraic spaces is smooth.
* `AlgebraicGeometry.Space.IsSmoothAt`: a morphism of algebraic spaces is smooth at a point of
  its source.

## References

* [Stacks Project, Tag 03ZC](https://stacks.math.columbia.edu/tag/03ZC)
-/


@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism of algebraic spaces over `S` is *smooth* when the scheme morphism underlying every
commuting square of étale scheme charts of it is smooth. -/
@[stacks 03ZC "part (1): smooth morphisms"]
abbrev IsSmooth (f : X ⟶ Y) : Prop :=
  HoldsOnEveryEtaleChart B S hS
    (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u}) f

/-- A morphism of algebraic spaces over `S` is *smooth at* a point `x` of its source when it is
smooth on some open subspace of the source having a point over `x`. -/
@[stacks 03ZC "part (2): smooth at a point"]
abbrev IsSmoothAt (f : X ⟶ Y) (x : points B S hS X) : Prop :=
  ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
    ∃ x' : points B S hS U.toFunctor,
      pointsMap B S hS U.toFunctor U.ι x' = x ∧ IsSmooth B S hS (U.ι ≫ f)

end AlgebraicGeometry.Space

end
