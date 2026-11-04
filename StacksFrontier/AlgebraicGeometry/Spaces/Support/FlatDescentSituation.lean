module

public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat

/-!
# A flat descent situation for algebraic spaces

Descent results for algebraic spaces are stated for a commutative triangle `X ⟶ Y ⟶ B` of
algebraic spaces over a base scheme `S` in which the first morphism is surjective, flat and
locally of finite presentation: such a morphism is an fppf covering of `Y` by `X`, so a datum
on `X` compatible with the two projections of `X ×_Y X` descends to `Y`, and a property of
`Y ⟶ B` may be tested on `X ⟶ B`. This file bundles that standing situation.

## Main definitions

* `AlgebraicGeometry.Space.CommonFppfDescentSituation` packages the triangle together with
  the surjectivity, flatness and local finite presentation of `X ⟶ Y`.

## Implementation notes

Algebraic spaces over `S` are presheaves on the big fppf site over `S` satisfying
`AlgebraicGeometry.IsAlgebraicSpace`; the three objects of the triangle are given as
presheaves with their algebraicity recorded as separate fields, so that the situation can be
assembled from data that is not already packaged as an object of
`AlgebraicGeometry.AlgebraicSpaces`. The equation `p = f ≫ q` expresses commutativity of the
triangle rather than defining `p`, which keeps the composite available under its own name in
the statements the situation feeds.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- A commutative triangle `X ⟶ Y ⟶ B` of algebraic spaces over a base scheme whose first
morphism is surjective, flat and locally of finite presentation. -/
structure CommonFppfDescentSituation where
  /-- The ambient big fppf site. -/
  site : BigFppfSite.{u}
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The base scheme belongs to the site. -/
  hS : site.Contains S
  /-- The source algebraic space. -/
  X : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u
  /-- The intermediate algebraic space. -/
  Y : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u
  /-- The target algebraic space. -/
  B : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u
  /-- The source is an algebraic space. -/
  algebraicSpaceX : IsAlgebraicSpace site S hS X
  /-- The intermediate object is an algebraic space. -/
  algebraicSpaceY : IsAlgebraicSpace site S hS Y
  /-- The target is an algebraic space. -/
  algebraicSpaceB : IsAlgebraicSpace site S hS B
  /-- The morphism from `X` to `Y`. -/
  f : X ⟶ Y
  /-- The morphism from `Y` to `B`. -/
  q : Y ⟶ B
  /-- The morphism from `X` to `B`. -/
  p : X ⟶ B
  /-- The triangle commutes. -/
  p_eq : p = f ≫ q
  /-- The morphism `f` is surjective. -/
  surjective_f : IsSurjective site S hS f
  /-- The morphism `f` is flat. -/
  flat_f : IsFlat site S hS f
  /-- The morphism `f` is locally of finite presentation. -/
  locallyOfFinitePresentation_f : IsLocallyOfFinitePresentation site S hS f

end AlgebraicGeometry.Space

end
