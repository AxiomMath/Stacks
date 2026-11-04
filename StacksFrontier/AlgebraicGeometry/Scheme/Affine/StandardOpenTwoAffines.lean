module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksCore.Tactic.StacksAttribute

/-!
# A common standard open of two affine opens

Given two affine opens `U` and `V` of a scheme and a point `x ∈ U ∩ V`, there is an open
neighbourhood of `x` which is a standard open of both `U` and `V`. Mathlib states this as
`AlgebraicGeometry.exists_basicOpen_le_affine_inter`: there are sections `f` on `U` and `g` on
`V` with `D(f) = D(g)` containing `x`. The common standard open `W = D(f)` is affine, being a
standard open of the affine open `U` (`AlgebraicGeometry.IsAffineOpen.basicOpen`).

## References

* [Stacks Project, Tag 01IW](https://stacks.math.columbia.edu/tag/01IW)
-/

@[expose] public section

add_to_stacks 01IW "the common standard open is `X.basicOpen f = X.basicOpen g`, affine as a
  standard open of the affine open `U`" AlgebraicGeometry.exists_basicOpen_le_affine_inter
