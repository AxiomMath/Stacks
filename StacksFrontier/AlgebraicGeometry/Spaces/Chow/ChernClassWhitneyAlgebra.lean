module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassInvertibleExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassWhitney

/-!
# The Whitney formula in the Chow cohomology ring

In Situation 0EDT let `X/B` be good and let `0 → ℰ₁ → ℰ → ℰ₂ → 0` be a short exact sequence of
finite locally free `𝒪_X`-modules, `ℰᵢ` of rank `rᵢ`. **Stacks 0ES9**: the total Chern classes
of Definition 0ERZ satisfy `c(ℰ) = c(ℰ₁) c(ℰ₂)` in the Chow cohomology ring `A^*(X)`.

`A^*(X)` is `AlgebraicGeometry.Space.ChowCohomologyAlgebra` (Stacks 0ERK), whose product is
composition of bivariant classes, and `c(ℰ)` is
`AlgebraicGeometry.Space.ChowCohomologyAlgebra.totalChernClass`, the sum of the bivariant classes
`c_j(ℰ)` of Stacks 0ERY, whose cap operations on every good test space are those of
`AlgebraicGeometry.Space.chernClass` (`ChowCohomologyClass.chernClass_cap_eq`).

## Proof

An element of `A^*(X)` is determined by its action on the Chow homology `CH_*(X')` of every good
test space `g : X' ⟶ X` (`ChowCohomologyAlgebra.ext_capChowHomology`), and that action is a ring
homomorphism `A^*(X) → End(CH_*(X'))`, under which `c(ℰ)` acts as the total Chern class of
`g^*ℰ` (`ChowCohomologyAlgebra.capChowHomology_totalChernClass_eq_totalChernCap`). The inverse
image `0 → g^*ℰ₁ → g^*ℰ → g^*ℰ₂ → 0` is again short exact, `g^*ℰ₂` being finite locally free
(`AlgebraicGeometry.Space.shortExact_map_modulePullback_of_isFiniteLocallyFreeOfRank`), of the
same ranks, so on `X'` the statement is the Whitney formula `c(g^*ℰ) = c(g^*ℰ₁) c(g^*ℰ₂)` of
operations on `CH_*(X')` (`AlgebraicGeometry.Space.totalChernCap_shortExact`).

## Main results

* `AlgebraicGeometry.Space.ChowCohomologyAlgebra.totalChernClass_shortExact`: **Stacks 0ES9**,
  `c(ℰ) = c(ℰ₁) c(ℰ₂)` in `A^*(X)`.
* `ChowCohomologyAlgebra.totalChernClass_eq_toChowCohomologyCanonical_mul_of_shortExact`: the
  same for `AlgebraicGeometry.Space.totalChernClass`, which is the image of `c(ℰ₁) c(ℰ₂)` in the
  graded group `AlgebraicGeometry.Space.chowCohomologyCanonical`.

## References

* [Stacks Project, Tag 0ES9](https://stacks.math.columbia.edu/tag/0ES9)
* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
* [Stacks Project, Tag 0ERK](https://stacks.math.columbia.edu/tag/0ERK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.ChowCohomologyAlgebra

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX}

/-- **Stacks 0ES9, the Whitney formula.** In Situation 0EDT let `X/B` be good and let
`0 → ℰ₁ → ℰ → ℰ₂ → 0` be a short exact sequence `T` of finite locally free `𝒪_X`-modules, `ℰ₁` of
rank `r₁` and `ℰ₂` of rank `r₂`, so that `ℰ` is finite locally free of rank `r₁ + r₂`
(`AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank.of_shortExact`). Then

  `c(ℰ) = c(ℰ₁) c(ℰ₂)`   in `A^*(X)`.

Here `A^*(X)` is the Chow cohomology ring of Stacks 0ERK
(`AlgebraicGeometry.Space.ChowCohomologyAlgebra`, the product being composition of bivariant
classes), and `c(-)` is the total Chern class of Definition 0ERZ
(`AlgebraicGeometry.Space.ChowCohomologyAlgebra.totalChernClass`), the sum of the bivariant
classes `c_j(-)` of Stacks 0ERY, whose cap operations on every good test space are those of
`AlgebraicGeometry.Space.chernClass` (`ChowCohomologyClass.chernClass_cap_eq`). -/
@[stacks 0ES9 "c(E) = c(E_1) c(E_2) in the Chow cohomology ring A^*(X) (ChowCohomologyAlgebra, \
product = composition of bivariant classes) for 0 → E_1 → E → E_2 → 0 exact with E_i finite \
locally free of rank r_i on a good X/B; c is the total Chern class of 0ERZ, the sum of the \
bivariant classes c_j of 0ERY, which cap as Space.chernClass on every test space"]
theorem totalChernClass_shortExact
    {T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem X hX.1)} (hT : T.ShortExact)
    {r₁ r₂ : ℕ}
    (h₁ : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) T.X₁ r₁)
    (h₂ : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) T.X₃ r₂) :
    ChowCohomologyAlgebra.totalChernClass D sX hX T.X₂ (r₁ + r₂)
        (RingedSite.IsFiniteLocallyFreeOfRank.of_shortExact _ hT h₁ h₂) =
      ChowCohomologyAlgebra.totalChernClass D sX hX T.X₁ r₁ h₁ *
        ChowCohomologyAlgebra.totalChernClass D sX hX T.X₃ r₂ h₂ := by
  refine ext_capChowHomology fun g hY => ?_
  rw [map_mul, capChowHomology_totalChernClass_eq_totalChernCap,
    capChowHomology_totalChernClass_eq_totalChernCap,
    capChowHomology_totalChernClass_eq_totalChernCap]
  have hT' := shortExact_map_modulePullback_of_isFiniteLocallyFreeOfRank
    (goodSpaceHom D sX hX g hY) T hT h₂
  exact totalChernCap_shortExact hY hT' _ _

/-- **Stacks 0ES9 for `AlgebraicGeometry.Space.totalChernClass`.** In the situation of
`AlgebraicGeometry.Space.ChowCohomologyAlgebra.totalChernClass_shortExact`, the total Chern class
`AlgebraicGeometry.Space.totalChernClass` of `ℰ` of Definition 0ERZ, an element of the graded
group of bivariant classes over the fibre products `X ×_X X'`
(`AlgebraicGeometry.Space.chowCohomologyCanonical`, which carries no product), is the image of the
product `c(ℰ₁) c(ℰ₂)` of the Chow cohomology ring `A^*(X)` under
`AlgebraicGeometry.Space.ChowCohomologyAlgebra.toChowCohomologyCanonical`, which sends the total
Chern classes of `A^*(X)` to those of `AlgebraicGeometry.Space.totalChernClass`
(`ChowCohomologyAlgebra.toChowCohomologyCanonical_totalChernClass`). -/
theorem totalChernClass_eq_toChowCohomologyCanonical_mul_of_shortExact
    {T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem X hX.1)} (hT : T.ShortExact)
    {r₁ r₂ : ℕ}
    (h₁ : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) T.X₁ r₁)
    (h₂ : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) T.X₃ r₂) :
    Space.totalChernClass D sX hX T.X₂ (r₁ + r₂)
        (RingedSite.IsFiniteLocallyFreeOfRank.of_shortExact _ hT h₁ h₂) =
      toChowCohomologyCanonical D sX hX
        (ChowCohomologyAlgebra.totalChernClass D sX hX T.X₁ r₁ h₁ *
          ChowCohomologyAlgebra.totalChernClass D sX hX T.X₃ r₂ h₂) := by
  rw [← totalChernClass_shortExact hT h₁ h₂, toChowCohomologyCanonical_totalChernClass]

end AlgebraicGeometry.Space.ChowCohomologyAlgebra

end
