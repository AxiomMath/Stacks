module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurves
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.CostructuredArrowUliftHoms

/-!
# The polarized families over a proper flat family, at the raised morphism universe

For a finitely presented, flat and proper family `X₀` of algebraic spaces over the big fppf site
of `Spec(ℤ)`, the category `CostructuredArrow (forgetPolarization B) X₀` of polarized families
over `X₀` is equivalent over the site to its counterpart for
`AlgebraicGeometry.forgetPolarizationUp`, whose morphisms live one universe up.

## Main definitions

* `AlgebraicGeometry.polarizedOverProperFlatUliftHoms`: the polarized families over `X₀` are
  equivalent over the site to the polarized families over `X₀` read at the raised morphism
  universe.

## References

* [Stacks Project, Tag 0D41](https://stacks.math.columbia.edu/tag/0D41)
* [Stacks Project, Tag 0DPY](https://stacks.math.columbia.edu/tag/0DPY)
* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (X₀ : CartesianProperFlatSpaces B integerBase hZ)

/-- **The polarized families over a finitely presented, flat and proper family of algebraic
spaces, read at the raised morphism universe.** The two categories have the same objects — a
polarized family together with an identification of its underlying family of algebraic spaces with
`X₀` — and the morphisms of the second are those of the first wrapped in `ULift`. The comparison is
an equivalence over the big fppf site of `Spec(ℤ)` in both directions, strictly. -/
def polarizedOverProperFlatUliftHoms :
    StacksRepresentableCFG.EquivalenceOver
      (CostructuredArrow.proj (forgetPolarization B) X₀ ⋙
        forgetPolarization B ⋙ cartesianProperFlatProjection B integerBase hZ)
      (CostructuredArrow.proj (forgetPolarizationUp B hZ) X₀ ⋙ polarizedProjectionOver B hZ) :=
  StacksRepresentableCFG.costructuredArrowUliftHoms (forgetPolarization B) X₀
    (forgetPolarization B ⋙ cartesianProperFlatProjection B integerBase hZ)

end AlgebraicGeometry

end
