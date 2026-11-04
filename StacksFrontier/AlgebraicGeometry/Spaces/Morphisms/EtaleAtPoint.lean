module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# Étaleness at a point of an algebraic space

A morphism of algebraic spaces over a scheme `S` is étale at a point of its source when its
restriction to some open neighbourhood of that point is étale.

## Main definitions

* `AlgebraicGeometry.Space.IsEtaleAt` is étaleness of a morphism of algebraic spaces at a
  point of its source.

## Implementation notes

An open neighbourhood of the point is an open subspace of the source, in the sense of
`AlgebraicGeometry.Space.IsOpenSubspace`, which contains it; containment means that the
point lies in the image of the induced map `AlgebraicGeometry.Space.pointsMap` of the
inclusion. The restriction of the morphism is the composite of that inclusion with it.

## References

* [Stacks Project, Tag 04RH](https://stacks.math.columbia.edu/tag/04RH)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- A morphism of algebraic spaces is étale at a point if it is étale on an open subspace
containing that point. -/
@[stacks 04RH]
abbrev IsEtaleAt (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (x : points B S hS X) : Prop :=
  ∃ (U : Subfunctor X), IsOpenSubspace B S hS U ∧
    ∃ x' : points B S hS U.toFunctor,
      pointsMap B S hS U.toFunctor U.ι x' = x ∧ IsEtale B S hS (U.ι ≫ f)

end AlgebraicGeometry.Space

end
