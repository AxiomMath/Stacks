module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassInvertibleTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernCapCanonicalComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackShortExactLocallyFree

/-!
# The total Chern class of an extension by an invertible module

In Situation 0EDT let `X/B` be good and let `0 → ℒ → ℰ → ℱ → 0` be a short exact sequence of
`𝒪_X`-modules with `ℒ` invertible and `ℰ`, `ℱ` finite locally free of ranks `r + 1` and `r`.
**Stacks 0ES8**: the total Chern classes of Definition 0ERZ satisfy `c(ℰ) = c(ℒ) c(ℱ)` in the
Chow cohomology ring `A^*(X)`.

`A^*(X)` is `AlgebraicGeometry.Space.ChowCohomologyAlgebra` (Stacks 0ERK), whose product is
composition of bivariant classes, and `c(ℰ)` is
`AlgebraicGeometry.Space.ChowCohomologyAlgebra.totalChernClass`, the sum of the bivariant classes
`c_j(ℰ)` of Stacks 0ERY: on a good test space `g : X' ⟶ X` the class `c_j(ℰ)` caps as
`AlgebraicGeometry.Space.chernCap`, which is also the cap operation of
`AlgebraicGeometry.Space.chernClass` (`ChowCohomologyClass.chernClass_cap_eq`).

## Proof

An element of `A^*(X)` is determined by its action on the Chow homology `CH_*(X')` of every good
test space `g : X' ⟶ X` (`ChowCohomologyAlgebra.ext_capChowHomology`), and that action is a ring
homomorphism `A^*(X) → End(CH_*(X'))`. On `CH_*(X')` the class `c(ℰ)` acts as the total Chern
class of `g^*ℰ` (`ChowCohomologyAlgebra.capChowHomology_totalChernClass_eq_totalChernCap`). The
inverse image `0 → g^*ℒ → g^*ℰ → g^*ℱ → 0` is again short exact, `g^*ℱ` being finite locally
free (`AlgebraicGeometry.Space.shortExact_map_modulePullback_of_isFiniteLocallyFreeOfRank`), with
`g^*ℒ` invertible and the same ranks, so the statement on `X'` is the identity
`c(g^*ℰ) = c(g^*ℒ) c(g^*ℱ)` of operations on `CH_*(X')`. That identity is assembled from the
degree-wise relation `c_{n+1}(ℰ) = c_{n+1}(ℱ) + c₁(ℒ) c_n(ℱ)`
(`AlgebraicGeometry.Space.PrivateChern.chernCap_succ_eq_of_shortExact`), the vanishing
`c_{r+1}(ℱ) = 0` and `c₀ = 1`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.totalChernCap_eq_mul_of_shortComplex`: `c(ℰ) = c(ℒ) c(ℱ)`
  as operations on `CH_*(X)`.
* `AlgebraicGeometry.Space.ChowCohomologyAlgebra.totalChernClass_eq_mul_of_shortExact`:
  **Stacks 0ES8**, `c(ℰ) = c(ℒ) c(ℱ)` in `A^*(X)`.
* `ChowCohomologyAlgebra.totalChernClass_eq_toChowCohomologyCanonical_mul`:
  the same for `AlgebraicGeometry.Space.totalChernClass`, which is the image of `c(ℒ) c(ℱ)` in
  the graded group `AlgebraicGeometry.Space.chowCohomologyCanonical`.

## References

* [Stacks Project, Tag 0ES8](https://stacks.math.columbia.edu/tag/0ES8)
* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
* [Stacks Project, Tag 0ERK](https://stacks.math.columbia.edu/tag/0ERK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace PrivateChern

variable {D : BaseSpaceDimensionSituation.{u}}

/-- **`c(ℰ) = c(ℒ) c(ℱ)` on `CH_*(X)`.** For a short exact sequence `0 → ℒ → ℰ → ℱ → 0` of
`𝒪_X`-modules on a good `X`, `ℒ` invertible and `ℰ`, `ℱ` finite locally free of ranks `r + 1`
and `r`, the total Chern classes, as operations on `CH_*(X)`, satisfy `c(ℰ) = c(ℒ) c(ℱ)`. -/
theorem totalChernCap_eq_mul_of_shortComplex {X : D.Ambient} {sX : X ⟶ D.space}
    (hX : D.IsGood sX) (r : ℕ) (T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem X hX.1))
    (hT : T.ShortExact) (h₁ : IsInvertibleModule (goodSpace hX) T.X₁)
    (h₂ : IsFiniteLocallyFreeOfRank D sX hX T.X₂ (r + 1))
    (h₃ : IsFiniteLocallyFreeOfRank D sX hX T.X₃ r) :
    totalChernCap.{u, u + 1} T.X₂ (r + 1) h₂ =
      totalChernCap.{u, u + 1} T.X₁ 1
          (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) h₁) *
        totalChernCap.{u, u + 1} T.X₃ r h₃ := by
  have h8 := chernCap_succ_eq_of_shortComplex hX r T hT h₁ h₂ h₃
  have hv : chernCap.{u, u + 1} T.X₃ r h₃ (r + 1) = 0 :=
    chernCap_eq_zero_of_lt_of_hasIntertwiningSplittings chernCap_succ_eq_of_shortComplex_all
      hasIntertwiningSplittings hX T.X₃ r h₃ (Nat.lt_succ_self r)
  simp only [totalChernCap]
  rw [Finset.sum_range_succ' (fun n => chernCap.{u, u + 1} T.X₂ (r + 1) h₂ n) (r + 1),
    show ∑ n ∈ Finset.range (1 + 1), chernCap.{u, u + 1} T.X₁ 1
        (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) h₁) n =
      1 + chernCap.{u, u + 1} T.X₁ 1
        (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) h₁) 1 by
      rw [Finset.sum_range_succ, Finset.sum_range_one, chernCap_zero]]
  simp only [h8, Finset.sum_add_distrib, ← Finset.mul_sum, chernCap_zero]
  rw [Finset.sum_range_succ (fun n => chernCap.{u, u + 1} T.X₃ r h₃ (n + 1)) r, hv, add_zero,
    Finset.sum_range_succ' (fun n => chernCap.{u, u + 1} T.X₃ r h₃ n) r, chernCap_zero, add_mul,
    one_mul]
  abel

end PrivateChern

namespace ChowCohomologyAlgebra

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX}

/-- **Stacks 0ES8.** In Situation 0EDT let `X/B` be good and let `ℰ`, `ℱ` be finite locally free
`𝒪_X`-modules of ranks `r + 1` and `r` which fit into a short exact sequence
`0 → ℒ → ℰ → ℱ → 0` with `ℒ` invertible. Then

  `c(ℰ) = c(ℒ) c(ℱ)`   in `A^*(X)`.

Here `A^*(X)` is the Chow cohomology ring of Stacks 0ERK
(`AlgebraicGeometry.Space.ChowCohomologyAlgebra`, the product being composition of bivariant
classes), and `c(-)` is the total Chern class of Definition 0ERZ
(`AlgebraicGeometry.Space.ChowCohomologyAlgebra.totalChernClass`), the sum of the bivariant
classes `c_j(-)` of Stacks 0ERY, whose cap operations on every good test space are those of
`AlgebraicGeometry.Space.chernClass` (`ChowCohomologyClass.chernClass_cap_eq`); `ℒ` has rank one.
The source's ranks `r`, `r - 1` are `r + 1`, `r` here. -/
@[stacks 0ES8 "c(E) = c(L) c(F) in the Chow cohomology ring A^*(X) (ChowCohomologyAlgebra, \
product = composition of bivariant classes) for 0 → L → E → F → 0 exact, L invertible, E, F \
finite locally free of ranks r + 1, r on a good X/B; c is the total Chern class of 0ERZ, the sum \
of the bivariant classes c_j of 0ERY, which cap as Space.chernClass on every test space"]
theorem totalChernClass_eq_mul_of_shortExact
    {L E F : Modules.{u, u} D.site D.base D.base_mem X hX.1}
    (i : L ⟶ E) (q : E ⟶ F) (hiq : i ≫ q = 0) (hC : (ShortComplex.mk i q hiq).ShortExact)
    (hL : IsInvertibleModule (PrivateChern.goodSpace hX) L) (r : ℕ)
    (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E (r + 1))
    (hF : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) F r) :
    ChowCohomologyAlgebra.totalChernClass D sX hX E (r + 1) hE =
      ChowCohomologyAlgebra.totalChernClass D sX hX L 1
          (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (PrivateChern.goodSpace hX) hL) *
        ChowCohomologyAlgebra.totalChernClass D sX hX F r hF := by
  refine ext_capChowHomology fun g hY => ?_
  rw [map_mul, capChowHomology_totalChernClass_eq_totalChernCap,
    capChowHomology_totalChernClass_eq_totalChernCap,
    capChowHomology_totalChernClass_eq_totalChernCap]
  have hT := shortExact_map_modulePullback_of_isFiniteLocallyFreeOfRank
    (goodSpaceHom D sX hX g hY) (ShortComplex.mk i q hiq) hC hF
  exact PrivateChern.totalChernCap_eq_mul_of_shortComplex hY r _ hT
    (modulePullbackInvertible (goodSpaceHom D sX hX g hY) L hL) _ _

/-- **Stacks 0ES8 for `AlgebraicGeometry.Space.totalChernClass`.** In the situation of
`AlgebraicGeometry.Space.ChowCohomologyAlgebra.totalChernClass_eq_mul_of_shortExact`, the total
Chern class `AlgebraicGeometry.Space.totalChernClass` of `ℰ` of Definition 0ERZ, an element of
the graded group of bivariant classes over the fibre products `X ×_X X'`
(`AlgebraicGeometry.Space.chowCohomologyCanonical`, which carries no product), is the image of
the product `c(ℒ) c(ℱ)` of the Chow cohomology ring `A^*(X)` under the map
`AlgebraicGeometry.Space.ChowCohomologyAlgebra.toChowCohomologyCanonical`, which sends the total
Chern classes of `A^*(X)` to those of `AlgebraicGeometry.Space.totalChernClass`
(`ChowCohomologyAlgebra.toChowCohomologyCanonical_totalChernClass`). -/
theorem totalChernClass_eq_toChowCohomologyCanonical_mul
    {L E F : Modules.{u, u} D.site D.base D.base_mem X hX.1}
    (i : L ⟶ E) (q : E ⟶ F) (hiq : i ≫ q = 0) (hC : (ShortComplex.mk i q hiq).ShortExact)
    (hL : IsInvertibleModule (PrivateChern.goodSpace hX) L) (r : ℕ)
    (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E (r + 1))
    (hF : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) F r) :
    Space.totalChernClass D sX hX E (r + 1) hE =
      toChowCohomologyCanonical D sX hX
        (ChowCohomologyAlgebra.totalChernClass D sX hX L 1
            (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (PrivateChern.goodSpace hX) hL) *
          ChowCohomologyAlgebra.totalChernClass D sX hX F r hF) := by
  rw [← totalChernClass_eq_mul_of_shortExact i q hiq hC hL r hE hF,
    toChowCohomologyCanonical_totalChernClass]

end ChowCohomologyAlgebra

end AlgebraicGeometry.Space

end
