module

public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.AbelianVariety.PicardSchemeSmooth
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.DegreeZero.OpenSubgroupScheme

/-!
# `Pic⁰_{X/k}` is smooth of dimension the genus

Let `X` be a smooth projective curve of genus `g` over an algebraically closed field `k` and let
`P` be a scheme of a big fppf site representing its Picard functor. The degree-zero open subgroup
scheme `Pic⁰_{X/k}` of `P` (`Stacks.PicardFunctor.degreeZeroOpenSubgroupScheme`) is smooth of
relative dimension `g` over `k`, being open in `P`
(`Stacks.PicardFunctor.smoothOfRelativeDimension_picardScheme_of_representableBy`).

## Main results

* `Stacks.PicardFunctor.smoothOfRelativeDimension_degreeZeroOpenSubgroupScheme`.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.PicardFunctor

/-- **`Pic⁰_{X/k}` is smooth of relative dimension the genus.** For a smooth projective curve
`X` over an algebraically closed field `k` and a scheme `P` of a big fppf site representing its
Picard functor, the degree-zero open subgroup scheme of `P` is smooth of relative dimension
`genus X` over `k`. -/
theorem smoothOfRelativeDimension_degreeZeroOpenSubgroupScheme
    (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) (k : Type u) [Field k]
    [IsAlgClosed k] {hk : B.Contains (Spec (.of k))} (g : B.obj hX ⟶ B.obj hk)
    [IsCurve k (B.inclusion.map g)] [IsProjectiveVariety k (B.inclusion.map g)]
    [Smooth (B.inclusion.map g)] {P : BigFppfOver B (Spec (.of k)) hk}
    (R : (picardFunctor B hX hk g).RepresentableBy P) :
    letI := representingGrpObj R
    SmoothOfRelativeDimension (genus (B.inclusion.map g))
      (degreeZeroOpenSubgroupScheme B hX k g R).carrier.X.hom := by
  let := representingGrpObj R
  have := smoothOfRelativeDimension_picardScheme_of_representableBy B hX k g R
  exact OpenSubgroupScheme.smoothOfRelativeDimension_carrier _ _

end Stacks.PicardFunctor

end
