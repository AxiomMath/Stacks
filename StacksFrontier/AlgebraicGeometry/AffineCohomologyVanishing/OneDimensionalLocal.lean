module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The affine-vanishing hypothesis of Tag 09N8

`Stacks.AlgebraicGeometry.OneDimensionalLocal.isZero_rightDerived_pushforward_of_isRetrocompact`
is [Stacks, Tag 09N8] stated from three hypotheses, one for each result the source cites that
was absent when it was proved. The first of the three,
`Stacks.AlgebraicGeometry.OneDimensionalLocal.HigherDirectImageVanishingAffine`, is
[Stacks, Tag 01XC]; this file discharges it from
`Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom`.

The hypothesis is phrased with `CategoryTheory.Functor.rightDerived`, indexed by `ℕ`, and the
tag is proved with `CategoryTheory.Functor.rightDerivedPlus`, indexed by `ℤ`. The two are
reconciled by `OneDimensionalLocal.higherDirectImageVanishingAffine_of_rightDerivedPlus`, which
rests on `Stacks.DerivedIndexing.isZero_rightDerived_obj_iff`.

## Main results

* `higherDirectImageVanishingAffine`: the first hypothesis of
  `isZero_rightDerived_pushforward_of_isRetrocompact`, proved.

## References

* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 09N8](https://stacks.math.columbia.edu/tag/09N8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.OneDimensionalLocal

/-- The higher direct images of a quasi-coherent module along an affine morphism of schemes
vanish in positive degrees, stated with the `ℕ`-indexed `CategoryTheory.Functor.rightDerived`.
This is [Stacks, Tag 01XC]. -/
@[ega "II 5.2.2" "a ⇒ c, a ⇒ c'"]
theorem higherDirectImageVanishingAffine : HigherDirectImageVanishingAffine.{u} :=
  higherDirectImageVanishingAffine_of_rightDerivedPlus fun q G hq hG i hi ↦ by
    have := hq
    have := hG
    exact Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom q G i hi

end Stacks.AlgebraicGeometry.OneDimensionalLocal

end
