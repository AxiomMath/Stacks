module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.AlgebraicGeometry.Thickenings

/-!
# Infinitesimal lifting diagrams for a morphism of algebraic stacks (Stacks 0DNX)

Formal smoothness of a morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks is a lifting condition
against the diagram displayed as equation 0DNX of the source: a first-order thickening
`i : T ⟶ T'` of affine schemes on the left, `f` on the right, a `T`-valued point `x` of `𝒳`,
a `T'`-valued point `y` of `𝒴`, and a 2-morphism `γ : y ∘ i ⟶ f ∘ x` witnessing that the
square 2-commutes. This module records that solid diagram together with its 2-commutativity
datum; the dotted arrows completing it are the general bicategorical notion
`CategoryTheory.DottedArrow` of Stacks 0H18.

## Main definitions

* `AlgebraicGeometry.Stack.InfinitesimalLiftingDiagram`: **Stacks 0DNX**, the solid part of a
  2-commutative infinitesimal lifting diagram.

## Implementation notes

The two schemes are objects `T`, `T'` of the big fppf site of `S`, and the thickening
condition is read on the underlying morphism of schemes `B.inclusion.map i.left`. They are
presented in the 2-category of categories fibred in groupoids by
`AlgebraicGeometry.Stack.schemeFibredCategory`, and the 1-morphism `j` between those
presentations is the one induced by `i`: the field `j_canonical` identifies its underlying functor
with `CategoryTheory.Over.map i`.

## References

* [Stacks Project, Tag 0DNX](https://stacks.math.columbia.edu/tag/0DNX)
-/

@[expose] public section

open CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u w

/-- The solid part of a 2-commutative infinitesimal lifting diagram for a
1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`: a first-order thickening of affine
objects of the big fppf site of `S`, a point of `𝒳` over the smaller one, a point of `𝒴` over
the larger one, and a 2-morphism witnessing that the square 2-commutes. -/
@[stacks 0DNX]
structure InfinitesimalLiftingDiagram
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS)
    (f : 𝒳 ⟶ 𝒴) where
  /-- The smaller object of the site. -/
  T : BigFppfOver B S hS
  /-- The larger object of the site. -/
  T' : BigFppfOver B S hS
  /-- The smaller scheme is affine. -/
  affine_T : IsAffine ((BigFppfOver.toScheme B S hS).obj T)
  /-- The larger scheme is affine. -/
  affine_T' : IsAffine ((BigFppfOver.toScheme B S hS).obj T')
  /-- The thickening, as a morphism of the site. -/
  i : T ⟶ T'
  /-- Its underlying morphism of schemes is a first-order thickening. -/
  thickening : Stacks.Thickenings.IsFirstOrderThickening (B.inclusion.map i.left)
  /-- The 1-morphism between the represented fibred categories. -/
  j : schemeFibredCategory B S hS T ⟶ schemeFibredCategory B S hS T'
  /-- It is the one induced by the thickening. -/
  j_canonical : j.hom.toFunctor = Over.map i
  /-- The point of the source over the smaller scheme. -/
  x : schemeFibredCategory B S hS T ⟶ 𝒳.1
  /-- The point of the target over the larger scheme. -/
  y : schemeFibredCategory B S hS T' ⟶ 𝒴.1
  /-- The 2-morphism witnessing 2-commutativity of the square. -/
  γ : (j ≫ y) ⟶ (x ≫ f.hom)

end AlgebraicGeometry.Stack

end
