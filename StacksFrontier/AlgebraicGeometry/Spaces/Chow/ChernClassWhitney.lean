module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernCapInvertibleSubmodule
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernCapShortExact

/-!
# The Whitney formula

In Situation 0EDT let `X/B` be good and let `0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` be a short exact sequence of
finite locally free `𝒪_X`-modules, `ℰ_i` of rank `r_i`. Then the total Chern classes, as
operations on `CH_*(X)`, satisfy `c(ℰ) = c(ℰ₁) c(ℰ₂)`; this is the input on every test space for
Stacks 0ES9 in `A^*(X)` (`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassWhitneyAlgebra`).

## Main results

* `AlgebraicGeometry.Space.totalChernCap_shortExact`: `c(ℰ) = c(ℰ₁) c(ℰ₂)` as operations on
  `CH_*(X)`; Stacks 0ES9 in `A^*(X)` is
  `AlgebraicGeometry.Space.ChowCohomologyAlgebra.totalChernClass_shortExact`.

## References

* [Stacks Project, Tag 0ES9](https://stacks.math.columbia.edu/tag/0ES9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Space.PrivateChern

universe u

namespace AlgebraicGeometry.Space

variable {D : BaseSpaceDimensionSituation.{u}}

/-- **The Whitney formula on `CH_*(X)`.** In Situation 0EDT let `X/B` be good and let
`0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` be a short exact sequence `T` of finite locally free `𝒪_X`-modules, `ℰ₁` of
rank `r₁` and `ℰ₂` of rank `r₂`; then `ℰ` is finite locally free of rank `r₁ + r₂`
(`AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank.of_shortExact`), and the total Chern
classes, as operations on `CH_*(X) = ⨁_k CH_k(X)` (`PrivateChern.totalChernCap`), satisfy
`c(ℰ) = c(ℰ₁) c(ℰ₂)`.

This is an identity of operations on the Chow homology of `X` alone. Stacks 0ES9, the identity in
the Chow cohomology ring `A^*(X)`, is
`AlgebraicGeometry.Space.ChowCohomologyAlgebra.totalChernClass_shortExact`, derived from this
statement on every good test space `X' ⟶ X`. -/
theorem totalChernCap_shortExact {X : D.Ambient} {sX : X ⟶ D.space} (hX : D.IsGood sX)
    {T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem X hX.1)} (hT : T.ShortExact)
    {r₁ r₂ : ℕ} (h₁ : PrivateChern.IsFiniteLocallyFreeOfRank D sX hX T.X₁ r₁)
    (h₂ : PrivateChern.IsFiniteLocallyFreeOfRank D sX hX T.X₃ r₂) :
    totalChernCap.{u, u + 1} T.X₂ (r₁ + r₂)
        (RingedSite.IsFiniteLocallyFreeOfRank.of_shortExact _ hT h₁ h₂) =
      totalChernCap.{u, u + 1} T.X₁ r₁ h₁ * totalChernCap.{u, u + 1} T.X₃ r₂ h₂ :=
  totalChernCap_shortExact_of_succ (fun hP r T hT h₁ h₂ h₃ n =>
    chernCap_succ_eq_of_shortComplex hP r T hT h₁ h₂ h₃ n) hX hT h₁ _ h₂

end AlgebraicGeometry.Space

end
