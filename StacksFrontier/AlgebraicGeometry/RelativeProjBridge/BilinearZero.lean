module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.Algebra

/-!
# A bilinear map of sheaves of modules vanishes on a zero argument

`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafBilinearMap` records an `𝒪_S`-bilinear map of
`𝒪_S`-modules as an additive map into additive maps, so it kills a zero argument on either side.
The two statements below are that fact, in the two arguments.

They are what a degreewise family of maps out of Situation 01NN's graded algebra needs in a
*mixed* bidegree, where one of the two source degrees is negative and their sum is not: the
homogeneous piece in the negative degree is a zero object, so the local section there is zero,
and both sides of a multiplicativity clause collapse — but only once the product of a zero
section with an arbitrary one is known to be zero, which is not a consequence of the piece in the
sum degree vanishing, because it does not.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafBilinearMap.app_zero_left` and
  `SheafBilinearMap.app_zero_right`: **a sheaf-level bilinear map sends a zero argument to the
  zero section**, in the first and in the second variable.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

variable {S : Scheme.{u}} {M N P : S.Modules}

namespace SheafBilinearMap

/-- A sheaf-level bilinear map sends a zero section in its first variable to the zero section:
the map on sections over an open is additive in that variable, so it carries `0` to the zero
additive map. -/
public theorem app_zero_left (B : SheafBilinearMap M N P) (U : S.Opens) (y : Γ(N, U)) :
    B.app U 0 y = 0 := by
  rw [map_zero]
  rfl

/-- A sheaf-level bilinear map sends a zero section in its second variable to the zero
section. -/
public theorem app_zero_right (B : SheafBilinearMap M N P) (U : S.Opens) (x : Γ(M, U)) :
    B.app U x 0 = 0 :=
  map_zero (B.app U x)

end SheafBilinearMap

end Stacks.AlgebraicGeometry.RelativeProjBridge

end
