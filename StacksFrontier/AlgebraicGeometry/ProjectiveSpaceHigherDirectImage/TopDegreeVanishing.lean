module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TopDegreeVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MiddleVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The top higher direct image of a twist vanishes above the complementary degree

Let `S` be a scheme, let `n = m + 1 ≥ 1`, let `d` be an integer and let `f : ℙⁿ_S ⟶ S` be the
structure morphism of projective `n`-space over `S`. The degree-`n` row of the display of
[Stacks, Tag 01XW] reads

`Rⁿ f_* 𝒪(d) = Hom_{𝒪_S}((𝒪_S[T₀, …, Tₙ])_{-n-1-d}, 𝒪_S)`,

and a polynomial algebra has no homogeneous part in a negative degree. In the range
`-n - 1 < d` the right-hand side is therefore the dual of the zero sheaf, so the row asserts the
vanishing

`Rⁿ f_* 𝒪(d) = 0` for `-n - 1 < d`,

which is what this file proves, over an arbitrary base and with no hypothesis on `d` beyond that
inequality.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage`
  `.isZero_rightDerivedPlus_pushforward_twistOver_top_of_lt`: **`Rⁿ f_* 𝒪(d) = 0` for
  `-n - 1 < d`**, for every scheme `S`, every `n = m + 1 ≥ 1` and every integer `d`.

## Implementation notes

The absolute vanishing is
`Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology_top_of_lt`, and the passage from it to
an arbitrary base is
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MiddleVanishing`
`.isZero_rightDerivedPlus_pushforward_twistOver_of_isZero`, which localises any absolute
vanishing of the cohomology of a twist, uniform in the coefficient ring, to a statement about
the higher direct image over an arbitrary base.

The hypothesis `n ≥ 1` is the one the degree-`n` row of the display carries. At `n = 0` the
degrees `q = 0` and `q = n` coincide and the display's first row is the one that applies:
`ℙ⁰_S = S` and `𝒪(d) = 𝒪_S` in every degree, so `R⁰ f_* 𝒪(d) = 𝒪_S` is not zero, while the
degree-`n` row would read `0` for every `d ≥ 0`.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MiddleVanishing
  (isZero_rightDerivedPlus_pushforward_twistOver_of_isZero)
open Stacks.ProjectiveSpace.Cohomology (isZero_twistCohomology_top_of_lt)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 2000] HasDerivedCategory.standard

/-- **`Rⁿ f_* 𝒪(d) = 0` for `-n - 1 < d`**, for the structure morphism `f : ℙⁿ_S ⟶ S` over an
arbitrary scheme `S`, for `n = m + 1 ≥ 1` and for every integer `d`.

This is the degree-`n` row of [Stacks, Tag 01XW] in the range where the sheaf it identifies
`Rⁿ f_* 𝒪(d)` with — the `𝒪_S`-dual of `(𝒪_S[T₀, …, Tₙ])_{-n-1-d}` — is the dual of the zero
sheaf, a polynomial algebra having no homogeneous part in a negative degree. -/
@[sga "6 VI 2.8" "partial"]
theorem isZero_rightDerivedPlus_pushforward_twistOver_top_of_lt (m : ℕ) (S : Scheme.{u}) {d : ℤ}
    (hd : -((m + 1 : ℕ) : ℤ) - 1 < d) :
    IsZero (((Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)).rightDerivedPlus
      ((m + 1 : ℕ) : ℤ)).obj (twistOver (m + 1) S d)) :=
  isZero_rightDerivedPlus_pushforward_twistOver_of_isZero (m + 1) S d (m + 1)
    fun R _ => isZero_twistCohomology_top_of_lt R m hd

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
