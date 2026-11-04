module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.Inputs
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Formula
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Bridge

/-!
# The top half of the projective bundle formula

For the projective bundle `π : P ⟶ X` of a finite locally free module of constant rank `r > 0` on
a scheme locally of finite type over the base of a Chow situation,
`π_*(c₁(𝒪(1))^{r-1} ∩ π^*β) = β` for every cycle class `β` on `X`.

## Main results

* `Stacks.Chow.GenuineChern.topHalf`: every Chow situation satisfies
  `Stacks.Chow.GenuineChern.TopHalf`.

## References

* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.GenuineChern

/-- For every scheme `X` locally of finite type over the base of `C` and the projective bundle
`π` of every finite locally free `𝒪_X`-module of constant rank `r > 0`,
`π_*(c₁(𝒪(1))^{r-1} ∩ π^*β) = β`. -/
theorem topHalf (C : ChowSituation.{u}) : TopHalf C := by
  intro X sX _ E n _ _ k β
  have := flat_bundleProj E n
  have := locallyOfFiniteType_bundleProj E n
  exact projectiveBundleProjection_top_of_bundleProjection C sX (bundleProj E ≫ sX)
    (bundleProj E) rfl n (relativeDimension_bundleProj E n)
    (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
    (bundleTwistCap E C sX) (fun k β ↦ projectiveBundle_projection_self E n C sX k β) k β

end Stacks.Chow.GenuineChern

end
