module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme

/-!
# The coordinate ring of the torus chart of the cubic surface

On the open subset `D₊(T₀ T₁ T₂)` of the cubic surface
`Y : T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3 - t T₀ T₁ T₂ = 0` of Stacks 0D5E, the coordinate `t` is the
function `(1 + x ^ 3 + y ^ 3) / (x y)` of the affine coordinates `x = T₁ / T₀` and `y = T₂ / T₀`,
so the chart is the two-dimensional torus `Spec k[x, y][1 / (x y)]`. This file names that ring,
its two coordinates, the function `t` on it, and the affine equation `1 + x ^ 3 + y ^ 3` of the
central fibre.

## Main definitions

* `Stacks.Examples.CurveFamilyNotScheme.torusRing`: `k[x, y][1 / (x y)]`.
* `Stacks.Examples.CurveFamilyNotScheme.torusFermat`: the affine Fermat equation
  `1 + x ^ 3 + y ^ 3` in `torusRing k`.
* `Stacks.Examples.CurveFamilyNotScheme.torusParameter`: the function
  `t = (1 + x ^ 3 + y ^ 3) / (x y)` in `torusRing k`.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open MvPolynomial

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

variable (k : Type u) [Field k]

/-- The coordinate ring `k[x, y][1 / (x y)]` of the two-dimensional torus over `k`. -/
abbrev torusRing : Type u :=
  Localization.Away (X 0 * X 1 : MvPolynomial (Fin 2) k)

/-- The affine Fermat equation `1 + x ^ 3 + y ^ 3`, as an element of the torus ring. -/
def torusFermat : torusRing k :=
  algebraMap (MvPolynomial (Fin 2) k) (torusRing k) (1 + X 0 ^ 3 + X 1 ^ 3)

/-- The function `t = (1 + x ^ 3 + y ^ 3) / (x y)` on the torus: on the torus chart of the cubic
surface this is the coordinate of the affine line. -/
def torusParameter : torusRing k :=
  torusFermat k * IsLocalization.Away.invSelf (X 0 * X 1 : MvPolynomial (Fin 2) k)

end Stacks.Examples.CurveFamilyNotScheme

end
