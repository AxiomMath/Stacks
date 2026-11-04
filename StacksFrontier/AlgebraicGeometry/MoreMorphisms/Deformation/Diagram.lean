module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import StacksFrontier.AlgebraicGeometry.Thickenings

/-!
# Cartesian finite-order deformation diagrams

An *infinitesimal deformation* of a morphism of schemes `f : X ⟶ Y` over a base `S` is the data
of a finite-order thickening `S ⟶ S'` of the base and a morphism `f' : X' ⟶ Y'` over `S'`
extending `f`, in which `X` and `Y` are recovered from `X'` and `Y'` by base change along
`S ⟶ S'`, and in which `X'` is flat over `S'`. This file bundles that situation.

Concretely the diagram consists of three thickenings `iS : S ⟶ S'`, `iX : X ⟶ X'` and
`iY : Y ⟶ Y'`, structure morphisms to the two bases, and the two horizontal morphisms `f` and
`f'`, subject to: `iS` is of finite order, `iX` and `iY` are thickenings, the two squares over
`iS` are cartesian, the horizontal morphisms are over their bases, they form a morphism of
thickenings, and `X' ⟶ S'` is flat.

## Main definitions

* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram` bundles the six schemes, their
  structure and comparison morphisms, and all the hypotheses of the situation.

## Implementation notes

The two cartesian squares are recorded by `CategoryTheory.IsPullback`, so their commutativity
is part of those fields; the remaining commutativity equations say that the two horizontal
morphisms are over their respective bases and that they form a morphism of thickenings. Nothing
is asserted beyond the standing data and hypotheses: the statements proved about the situation
live in the files that consume it.

## References

* [Stacks Project, Tag 06AG](https://stacks.math.columbia.edu/tag/06AG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Thickenings

universe u

/-- A cartesian diagram of thickenings of schemes over a finite-order thickening of the base,
with the enlarged source flat over the enlarged base. -/
structure CartesianFiniteOrderDeformationDiagram where
  /-- The closed subscheme of the base thickening. -/
  S : Scheme.{u}
  /-- The ambient scheme of the base thickening. -/
  S' : Scheme.{u}
  /-- The base thickening. -/
  iS : S ⟶ S'
  /-- The base thickening is of finite order. -/
  iS_finiteOrder : IsFiniteOrderThickening iS
  /-- The closed subscheme of the source thickening. -/
  X : Scheme.{u}
  /-- The ambient scheme of the source thickening. -/
  X' : Scheme.{u}
  /-- The source thickening. -/
  iX : X ⟶ X'
  /-- The source inclusion is a thickening. -/
  iX_thickening : IsThickening iX
  /-- The closed subscheme of the target thickening. -/
  Y : Scheme.{u}
  /-- The ambient scheme of the target thickening. -/
  Y' : Scheme.{u}
  /-- The target thickening. -/
  iY : Y ⟶ Y'
  /-- The target inclusion is a thickening. -/
  iY_thickening : IsThickening iY
  /-- The structure morphism of the source over the base. -/
  pX : X ⟶ S
  /-- The structure morphism of the enlarged source over the enlarged base. -/
  pX' : X' ⟶ S'
  /-- The structure morphism of the target over the base. -/
  pY : Y ⟶ S
  /-- The structure morphism of the enlarged target over the enlarged base. -/
  pY' : Y' ⟶ S'
  /-- The morphism of closed subschemes. -/
  f : X ⟶ Y
  /-- The morphism of ambient schemes. -/
  f' : X' ⟶ Y'
  /-- The morphism of closed subschemes is over the base. -/
  f_over_S : f ≫ pY = pX
  /-- The morphism of ambient schemes is over the enlarged base. -/
  f'_over_S' : f' ≫ pY' = pX'
  /-- The two horizontal morphisms form a morphism of thickenings. -/
  f_thickening_comm : f ≫ iY = iX ≫ f'
  /-- The source is the base change of the enlarged source. -/
  X_cartesian : IsPullback iX pX pX' iS
  /-- The target is the base change of the enlarged target. -/
  Y_cartesian : IsPullback iY pY pY' iS
  /-- The enlarged source is flat over the enlarged base. -/
  X'_flat : Flat pX'

end Stacks.Thickenings

end
