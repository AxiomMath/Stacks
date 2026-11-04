module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernCapInvertibleSubmodule
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernCapShortExact

/-!
# The Whitney formula

In Situation 0EDT let `X/B` be good and let `0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` be a short exact sequence of
finite locally free `𝒪_X`-modules, `ℰ_i` of rank `r_i`. Then the total Chern classes satisfy
`c(ℰ) = c(ℰ₁) c(ℰ₂)` (Stacks 0ES9).

## Main results

* `AlgebraicGeometry.Space.totalChernCap_shortExact`: Stacks 0ES9.

## References

* [Stacks Project, Tag 0ES9](https://stacks.math.columbia.edu/tag/0ES9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Space.PrivateChern

universe u

namespace AlgebraicGeometry.Space

variable {D : BaseSpaceDimensionSituation.{u}}

/-- **Stacks 0ES9, the Whitney formula.** In Situation 0EDT let `X/B` be good and let
`0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` be a short exact sequence `T` of finite locally free `𝒪_X`-modules, `ℰ₁` of
rank `r₁` and `ℰ₂` of rank `r₂`; then `ℰ` is finite locally free of rank `r₁ + r₂`
(`AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank.of_shortExact`). The total Chern classes
satisfy `c(ℰ) = c(ℰ₁) c(ℰ₂)`.

The Chern classes are those of Stacks 0ERZ, `c_n(ℰ) ∩ -` on `CH_*(X)` (`chernCap`), and
`c(ℰ) = c_0(ℰ) + ⋯ + c_r(ℰ)` (`totalChernCap`). An identity in `A^*(X)` is an identity of the
operations on `CH_*(Y)` for every good `Y ⟶ X`; the operation of `c_n(ℰ)` on `CH_*(Y)` is
`c_n(f^*ℰ) ∩ -`, and the inverse image along `f` of a short exact sequence of finite locally free
modules is again one, of modules of the same ranks, so the statement for all good `X` is the
statement in `A^*(X)`. -/
@[stacks 0ES9]
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
