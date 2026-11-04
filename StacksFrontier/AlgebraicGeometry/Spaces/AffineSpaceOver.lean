module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Relative affine space over an algebraic space

Affine `n`-space over a presheaf `X` on the big fppf site of `S` is the product of `X` with
the restricted functor of points of affine `n`-space over `S`.  A morphism into it over `X`
is a morphism into its second factor, so for `X` the functor of points of a scheme the
construction agrees with affine `n`-space over that scheme.

## Main definitions

* `AlgebraicGeometry.Space.affineSpaceOver` is relative affine `n`-space over a presheaf on
  the big fppf site of `S`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Relative affine `n`-space over a presheaf on the big fppf site of `S`**: the product of
the presheaf with the restricted functor of points of affine `n`-space over `S`.

The first projection is the structure morphism, so a morphism `j` into it lies over `f` when
`j ≫ prod.fst = f`, and its second component is a system of `n` coordinates. -/
noncomputable abbrev affineSpaceOver
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (n : ℕ) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  X ⨯ points (Over.post B.inclusion) (Over.mk (AffineSpace.over (ULift.{u} (Fin n)) S).hom)

end AlgebraicGeometry.Space

end
